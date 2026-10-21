/*
 * scrimplay - standalone Linux player for Scrimshaw scores
 * (format + synth ported from https://tools.simonwillison.net/scrimshaw-jukebox)
 *
 * Build:  cc -O2 -o scrimplay scrimplay.c -lm -lasound            (ALSA)
 *         cc -O2 -DUSE_SDL -o scrimplay scrimplay.c -lm $(sdl2-config --cflags --libs)
 *         cc -O2 -DNO_AUDIO -o scrimplay scrimplay.c -lm           (wav/raw only)
 *
 * Usage:  scrimplay [opts] [song.txt | -]      (reads stdin when piped)
 *   -w FILE  render to WAV instead of the sound card
 *   -r       raw s16le stereo 48k to stdout (pipe into aplay/sox)
 *   -l N     loop the "loop" section N times then stop (default: forever live, 1 for -w/-r)
 *   -t SEC   stop after SEC seconds
 *   -v VOL   master volume (default 1.0)
 *   -c       check only: print score errors, exit 1 if any
 *   -q       no scrolling view        -n  no colours
 *
 * The parser/compiler is a line-by-line port of the jukebox's ScrimScore.
 * The synth mirrors ScrimSynth's Web Audio graphs (same oscillators, envelopes,
 * biquads, Karplus-Strong plucks, compressor/limiter) on a tiny per-note node
 * engine. The 2.8 s convolution reverb is replaced by a calibrated Freeverb.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <math.h>
#include <ctype.h>
#include <stdint.h>
#include <signal.h>
#include <unistd.h>
#include <sys/ioctl.h>
#if !defined(NO_AUDIO) && !defined(USE_SDL)
#include <alsa/asoundlib.h>
#endif
#ifdef USE_SDL
#include <SDL.h>
#endif

#define SR 48000
#define NYQ (SR / 2.0)
#define BLK 64
#define clampf(x, a, b) ((x) < (a) ? (a) : (x) > (b) ? (b) : (x))
static float frand(void) { return (float)rand() / (float)RAND_MAX; }
static double mtof(double m) { return 440.0 * pow(2.0, (m - 69) / 12.0); }

/* ======================================================================
 *  SCORE PARSER / COMPILER  (port of ScrimScore)
 * ====================================================================== */
static const char *MELODIC[] = {"steeldrum", "marimba", "vibes", "celesta", "glock", "xylophone", "musicbox", "bell",
  "organ", "pipe", "strings", "pad", "choir", "voices", "brass", "trumpet", "horn", "tuba",
  "flute", "clarinet", "oboe", "bassoon", "accordion", "fiddle",
  "harp", "guitar", "banjo", "harpsichord", "pizz", "upright", "fretless", "synbass", "timpani",
  "chip", "sine", "square", "saw", "triangle", 0};
static const char *DRUMS[] = {"kick", "snare", "rim", "hat", "ohat", "ride", "crash", "shaker", "tamb",
  "conga", "tumba", "bongo", "bongolo", "clave", "block", "cowbell", "guiro",
  "tomlo", "tommid", "tomhi", "bodhran", "timbale", "tri", "clap", "gong", "thunder", "surf", 0};
static int lookup(const char **list, const char *s) { for (int i = 0; list[i]; i++) if (!strcmp(list[i], s)) return i; return -1; }

typedef struct { int line; char msg[300]; } Err;
static Err *errs; static int nerr, cerr_;
static void err(int ln, const char *fmt, ...) {
  if (nerr == cerr_) { cerr_ = cerr_ ? cerr_ * 2 : 32; errs = realloc(errs, cerr_ * sizeof(Err)); }
  va_list ap; va_start(ap, fmt); vsnprintf(errs[nerr].msg, sizeof errs[nerr].msg, fmt, ap); va_end(ap);
  errs[nerr++].line = ln;
}

static int pcl(char c) { static const int P[] = {9, 11, 0, 2, 4, 5, 7}; c = tolower(c); return (c >= 'a' && c <= 'g') ? P[c - 'a'] : -100; }
/* parse [A-Ga-g](##|bb|#|b)?[0-8] at s, return chars consumed (0 = no match) and midi */
static int note_at(const char *s, int *midi) {
  int pc = pcl(s[0]); if (pc < 0) return 0;
  int i = 1, acc = 0;
  if (s[1] == '#' && s[2] == '#') { acc = 2; i = 3; } else if (s[1] == 'b' && s[2] == 'b' && s[3] >= '0' && s[3] <= '8') { acc = -2; i = 3; }
  else if (s[1] == '#') { acc = 1; i = 2; } else if (s[1] == 'b' && s[2] >= '0' && s[2] <= '8') { acc = -1; i = 2; }
  if (s[i] < '0' || s[i] > '8') return 0;
  *midi = 12 * (s[i] - '0' + 1) + pc + acc; return i + 1;
}
static int note_to_midi(const char *s) { int m; int n = note_at(s, &m); return (n && s[n] == 0) ? m : -1; }

static const struct { const char *n; int iv[6]; int k; } CHORDS[] = {
  {"", {0, 4, 7}, 3}, {"maj", {0, 4, 7}, 3}, {"m", {0, 3, 7}, 3}, {"min", {0, 3, 7}, 3},
  {"7", {0, 4, 7, 10}, 4}, {"m7", {0, 3, 7, 10}, 4}, {"maj7", {0, 4, 7, 11}, 4}, {"mmaj7", {0, 3, 7, 11}, 4},
  {"6", {0, 4, 7, 9}, 4}, {"m6", {0, 3, 7, 9}, 4}, {"9", {0, 4, 7, 10, 14}, 5}, {"m9", {0, 3, 7, 10, 14}, 5},
  {"maj9", {0, 4, 7, 11, 14}, 5}, {"add9", {0, 4, 7, 14}, 4}, {"madd9", {0, 3, 7, 14}, 4},
  {"sus2", {0, 2, 7}, 3}, {"sus4", {0, 5, 7}, 3}, {"sus", {0, 5, 7}, 3}, {"7sus4", {0, 5, 7, 10}, 4},
  {"dim", {0, 3, 6}, 3}, {"dim7", {0, 3, 6, 9}, 4}, {"m7b5", {0, 3, 6, 10}, 4}, {"aug", {0, 4, 8}, 3}, {"+", {0, 4, 8}, 3},
  {"5", {0, 7}, 2}, {"7b9", {0, 4, 7, 10, 13}, 5}, {0, {0}, 0}};
static int place_near(int pc, int lo) { return lo + (((pc - lo) % 12) + 12) % 12; }
static int cmpint(const void *a, const void *b) { return *(int *)a - *(int *)b; }
/* "Dm7" or "C/E" -> notes near center; returns count, -1 if unknown */
static int chord_to_midis(const char *sym, int center, int *out) {
  if (sym[0] < 'A' || sym[0] > 'G') return -1;
  int root = pcl(sym[0]), i = 1;
  if (sym[i] == '#') { root++; i++; } else if (sym[i] == 'b') { root--; i++; }
  root = (root + 12) % 12;
  char q[32]; int j = 0;
  while (sym[i] && sym[i] != '/' && j < 31) q[j++] = sym[i++];
  q[j] = 0;
  int bass = -1;
  if (sym[i] == '/') {
    i++; if (sym[i] < 'A' || sym[i] > 'G') return -1;
    bass = pcl(sym[i++]);
    if (sym[i] == '#') { bass++; i++; } else if (sym[i] == 'b') { bass--; i++; }
    if (sym[i]) return -1;
    bass = (bass + 12) % 12;
  } else if (sym[i]) return -1;
  int c = -1; for (int k = 0; CHORDS[k].n; k++) if (!strcmp(CHORDS[k].n, q)) { c = k; break; }
  if (c < 0) return -1;
  int lo = center - 6, n = 0;
  int cand[8], nc = 0;
  for (int k = 0; k < CHORDS[c].k; k++) cand[nc++] = place_near((root + CHORDS[c].iv[k]) % 12, lo);
  if (bass >= 0) cand[nc++] = place_near(bass, lo - 12);
  for (int k = 0; k < nc; k++) { int dup = 0; for (int m = 0; m < n; m++) if (out[m] == cand[k]) dup = 1; if (!dup) out[n++] = cand[k]; }
  qsort(out, n, sizeof(int), cmpint);
  return n;
}

static float numf(const char *s, float lo, float hi, float def) {
  char *e; double n = strtod(s, &e);
  if (e == s || !isfinite(n)) return def;
  return clampf((float)n, lo, hi);
}
static int is_ident(const char *s) { if (!(isalpha((unsigned char)*s) || *s == '_')) return 0; for (s++; *s; s++) if (!(isalnum((unsigned char)*s) || *s == '_')) return 0; return 1; }

typedef struct {
  char name[40]; int inst; int drum;
  float vol, pan, rev, glide, gate, bright, att, rel; int trans, center, ln;
} Voice;
typedef struct { char **bars; int *lns; int n, cap; } RawVoice;
typedef struct {
  char name[40], from[40]; int ln;
  float tempo, swing; int beats, steps; int has_tempo, has_beats, has_steps, has_swing;
  char (*vnames)[40]; RawVoice **raw; int nv;
  char (*mute)[40]; int nmute;
} Pattern;
typedef struct { char name[40]; int trans, times, ln; } Ref;

#define MAXV 64
static struct {
  char title[200], composer[200], about[400];
  float tempo, swing, reverb; int beats, steps;
  Voice v[MAXV]; int nv;
  Pattern *pat; int npat;
  Ref *play, *loop; int nplay, nloop;
} song;

static int find_voice(const char *n) { for (int i = 0; i < song.nv; i++) if (!strcmp(song.v[i].name, n)) return i; return -1; }
static int find_pat(const char *n) { for (int i = 0; i < song.npat; i++) if (!strcmp(song.pat[i].name, n)) return i; return -1; }

static void parse_voice(char **w, int nw, int ln) {
  if (nw < 2) { err(ln, "Write voices as: voice NAME INSTRUMENT [options]"); return; }
  if (!is_ident(w[0])) { err(ln, "Voice name \"%s\" should use letters, digits and _.", w[0]); return; }
  char inst[40]; snprintf(inst, sizeof inst, "%s", w[1]); for (char *c = inst; *c; c++) *c = tolower(*c);
  int d = lookup(DRUMS, inst), m = lookup(MELODIC, inst);
  if (d < 0 && m < 0) { err(ln, "Unknown instrument \"%s\".", w[1]); return; }
  Voice v = {0};
  snprintf(v.name, sizeof v.name, "%s", w[0]);
  v.drum = d >= 0; v.inst = d >= 0 ? d : m;
  v.vol = .8f; v.pan = 0; v.rev = -1; v.trans = 0; v.glide = .07f; v.gate = 1; v.center = 62; v.bright = 1; v.att = 0; v.rel = 0; v.ln = ln;
  for (int i = 2; i < nw; i++) {
    char *eq = strchr(w[i], '=');
    if (!eq || eq == w[i] || !eq[1]) { err(ln, "Voice options look like key=value; got \"%s\".", w[i]); continue; }
    char k[32]; int kl = eq - w[i]; if (kl > 31) kl = 31; memcpy(k, w[i], kl); k[kl] = 0;
    for (char *c = k; *c; c++) *c = tolower(*c);
    const char *val = eq + 1;
    if (!strcmp(k, "vol")) v.vol = numf(val, 0, 2, .8f);
    else if (!strcmp(k, "pan")) v.pan = numf(val, -1, 1, 0);
    else if (!strcmp(k, "rev")) v.rev = numf(val, 0, 1, .2f);
    else if (!strcmp(k, "trans")) v.trans = (int)lroundf(numf(val, -48, 48, 0));
    else if (!strcmp(k, "oct")) v.trans += 12 * (int)lroundf(numf(val, -4, 4, 0));
    else if (!strcmp(k, "glide")) v.glide = numf(val, .005f, 2, .07f);
    else if (!strcmp(k, "gate")) v.gate = numf(val, .05f, 1, 1);
    else if (!strcmp(k, "bright")) v.bright = numf(val, .1f, 4, 1);
    else if (!strcmp(k, "att")) v.att = numf(val, .001f, 4, .01f);
    else if (!strcmp(k, "rel")) v.rel = numf(val, .005f, 6, .1f);
    else if (!strcmp(k, "center")) { int mm = note_to_midi(val); if (mm < 0) err(ln, "center= needs a note like E4; got \"%s\".", val); else v.center = mm; }
    else err(ln, "Unknown voice option \"%s\".", k);
  }
  if (find_voice(v.name) >= 0) err(ln, "Voice \"%s\" is declared twice.", v.name);
  else if (song.nv < MAXV) song.v[song.nv++] = v;
}

static char *trim(char *s) { while (isspace((unsigned char)*s)) s++; char *e = s + strlen(s); while (e > s && isspace((unsigned char)e[-1])) *--e = 0; return s; }

static void parse(char *text) {
  memset(&song, 0, sizeof song);
  strcpy(song.title, "Untitled"); song.tempo = 120; song.beats = 4; song.steps = 4; song.swing = 0; song.reverb = .3f;
  Pattern *cur = NULL; int ln = 0;
  for (char *line = text, *next; line; line = next) {
    next = strchr(line, '\n'); if (next) *next++ = 0;
    ln++;
    /* strip comment: '#' at start or after whitespace */
    for (char *c = line; *c; c++) if (*c == '#' && (c == line || isspace((unsigned char)c[-1]))) { *c = 0; break; }
    char *l = trim(line);
    if (!*l) continue;
    /* voice line: IDENT \s* | ... */
    { char *p = l; if (isalpha((unsigned char)*p) || *p == '_') { while (isalnum((unsigned char)*p) || *p == '_') p++; char *q = p; while (isspace((unsigned char)*q)) q++;
        if (*q == '|') {
          if (!cur) { err(ln, "Music lines go inside a pattern. Add a \"pattern NAME\" line above this one."); continue; }
          char vn[40]; int n = p - l; if (n > 39) n = 39; memcpy(vn, l, n); vn[n] = 0;
          char *body = q + 1;
          char *parts[512]; int np = 0;
          for (char *s = body;;) { char *bar = strchr(s, '|'); if (bar) *bar = 0; if (np < 512) parts[np++] = trim(s); if (!bar) break; s = bar + 1; }
          while (np && !*parts[np - 1]) np--;
          int vi = -1; for (int k = 0; k < cur->nv; k++) if (!strcmp(cur->vnames[k], vn)) vi = k;
          if (vi < 0) { cur->vnames = realloc(cur->vnames, (cur->nv + 1) * 40); cur->raw = realloc(cur->raw, (cur->nv + 1) * sizeof(RawVoice *));
            strcpy(cur->vnames[cur->nv], vn); cur->raw[cur->nv] = calloc(1, sizeof(RawVoice)); vi = cur->nv++; }
          RawVoice *rv = cur->raw[vi];
          for (int k = 0; k < np; k++) {
            if (!*parts[k]) { err(ln, "Empty bar %d in \"%s\". Use _ for a silent bar.", k + 1, vn); continue; }
            if (rv->n == rv->cap) { rv->cap = rv->cap ? rv->cap * 2 : 16; rv->bars = realloc(rv->bars, rv->cap * sizeof(char *)); rv->lns = realloc(rv->lns, rv->cap * sizeof(int)); }
            rv->bars[rv->n] = strdup(parts[k]); rv->lns[rv->n++] = ln;
          }
          continue;
        } } }
    char *words[256]; int nw = 0; char buf[4096]; snprintf(buf, sizeof buf, "%s", l);
    for (char *t = strtok(buf, " \t\r"); t && nw < 256; t = strtok(NULL, " \t\r")) words[nw++] = t;
    char kw[32]; snprintf(kw, sizeof kw, "%s", words[0]); for (char *c = kw; *c; c++) *c = tolower(*c);
    char *rest = trim(l + strlen(words[0]));
    #define TGT(field, hasf, val) do { if (cur) { cur->field = (val); cur->hasf = 1; } else song.field = (val); } while (0)
    if (!strcmp(kw, "title")) { if (*rest) snprintf(song.title, sizeof song.title, "%s", rest); }
    else if (!strcmp(kw, "composer") || !strcmp(kw, "by")) snprintf(song.composer, sizeof song.composer, "%s", rest);
    else if (!strcmp(kw, "about")) snprintf(song.about, sizeof song.about, "%s", rest);
    else if (!strcmp(kw, "tempo")) TGT(tempo, has_tempo, numf(rest, 20, 400, 120));
    else if (!strcmp(kw, "beats")) TGT(beats, has_beats, (int)lroundf(numf(rest, 1, 16, 4)));
    else if (!strcmp(kw, "steps")) TGT(steps, has_steps, (int)lroundf(numf(rest, 1, 12, 4)));
    else if (!strcmp(kw, "swing")) TGT(swing, has_swing, numf(rest, 0, .75f, 0));
    else if (!strcmp(kw, "reverb")) song.reverb = numf(rest, 0, 1, .3f);
    else if (!strcmp(kw, "voice")) parse_voice(words + 1, nw - 1, ln);
    else if (!strcmp(kw, "pattern")) {
      if (nw < 2 || !is_ident(words[1])) { err(ln, "Pattern names use letters, digits and _ (for example: pattern A2)."); cur = NULL; continue; }
      int pi = find_pat(words[1]);
      if (pi >= 0) err(ln, "Pattern \"%s\" is defined twice; the later one wins.", words[1]);
      else { song.pat = realloc(song.pat, (song.npat + 1) * sizeof(Pattern)); pi = song.npat++; }
      cur = &song.pat[pi]; memset(cur, 0, sizeof *cur);
      snprintf(cur->name, sizeof cur->name, "%s", words[1]); cur->ln = ln;
      for (int k = 2; k < nw; k++) {
        if (!strcasecmp(words[k], "from")) { if (k + 1 < nw) snprintf(cur->from, 40, "%s", words[++k]); continue; }
        char *eq = strchr(words[k], '=');
        if (!eq || eq == words[k] || !eq[1]) { err(ln, "Can't read \"%s\" in the pattern line.", words[k]); continue; }
        *eq = 0; for (char *c = words[k]; *c; c++) *c = tolower(*c);
        if (!strcmp(words[k], "tempo")) { cur->tempo = numf(eq + 1, 20, 400, 120); cur->has_tempo = 1; }
        else if (!strcmp(words[k], "beats")) { cur->beats = (int)lroundf(numf(eq + 1, 1, 16, 4)); cur->has_beats = 1; }
        else if (!strcmp(words[k], "steps")) { cur->steps = (int)lroundf(numf(eq + 1, 1, 12, 4)); cur->has_steps = 1; }
        else if (!strcmp(words[k], "swing")) { cur->swing = numf(eq + 1, 0, .75f, 0); cur->has_swing = 1; }
        else err(ln, "Unknown pattern option \"%s\".", words[k]);
      }
    } else if (!strcmp(kw, "mute")) {
      if (!cur) err(ln, "\"mute\" only works inside a pattern.");
      else for (int k = 1; k < nw; k++) { cur->mute = realloc(cur->mute, (cur->nmute + 1) * 40); snprintf(cur->mute[cur->nmute++], 40, "%s", words[k]); }
    } else if (!strcmp(kw, "play") || !strcmp(kw, "loop")) {
      cur = NULL;
      int isplay = kw[0] == 'p';
      for (int k = 1; k < nw; k++) {
        char *w = words[k]; Ref r = {{0}, 0, 1, ln};
        char *p = w; if (!(isalpha((unsigned char)*p) || *p == '_')) goto bad;
        while (isalnum((unsigned char)*p) || *p == '_') p++;
        /* non-greedy name: a trailing digit run belongs to the name unless +/- follows... JS: ([A-Za-z_]\w*?)([+-]\d+)?(?:\*(\d+))?$ */
        { int n = p - w; if (n > 39) n = 39; memcpy(r.name, w, n); r.name[n] = 0; }
        if (*p == '+' || *p == '-') { char *e; long t = strtol(p, &e, 10); if (e == p + 1) goto bad; r.trans = (int)t; p = e; }
        if (*p == '*') { char *e; long t = strtol(p + 1, &e, 10); if (e == p + 1) goto bad; r.times = t > 64 ? 64 : (int)t; p = e; }
        if (*p) goto bad;
        if (isplay) { song.play = realloc(song.play, (song.nplay + 1) * sizeof(Ref)); song.play[song.nplay++] = r; }
        else { song.loop = realloc(song.loop, (song.nloop + 1) * sizeof(Ref)); song.loop[song.nloop++] = r; }
        continue;
      bad: err(ln, "Can't read \"%s\". Write a pattern name, optionally with +N/-N to transpose and *N to repeat.", w);
      }
    } else err(ln, "Unknown line \"%s\". Lines start with a setting (title, tempo, voice, pattern, play, loop...) or a voice name followed by |.", words[0]);
  }
}

/* ---------------------------------------------------- pattern bodies */
#define MAXN 16
typedef struct { int step, len, n; int notes[MAXN]; float vel; int glide; char label[12]; } PEv;
typedef struct { PEv *e; int n, cap; } PEvList;
static PEv *pev_push(PEvList *l) { if (l->n == l->cap) { l->cap = l->cap ? l->cap * 2 : 32; l->e = realloc(l->e, l->cap * sizeof(PEv)); } memset(&l->e[l->n], 0, sizeof(PEv)); return &l->e[l->n++]; }

static float vel_from(const char *marks, int n) { float v = .8f; for (int i = 0; i < n; i++) v *= marks[i] == '!' ? 1.25f : .6f; return v > 1.35f ? 1.35f : v; }

static int cur_errln_bars(RawVoice *rv, int bi) { return bi < rv->n ? rv->lns[bi] : rv->lns[0]; }

static PEvList parse_melodic(RawVoice *rv, int barSteps, Voice *voice, const char *pname) {
  PEvList ev = {0}; int last = -1; /* index into ev, -1 = none */
  for (int bi = 0; bi < rv->n; bi++) {
    int start = bi * barSteps, eln = cur_errln_bars(rv, bi);
    char where[160]; snprintf(where, sizeof where, "bar %d of \"%s\" in pattern %s", bi + 1, voice->name, pname);
    const char *b = rv->bars[bi];
    if (!strcmp(b, "%")) {
      if (bi == 0) err(eln, "%% in %s has no previous bar to repeat.", where);
      int n0 = ev.n;
      for (int k = 0; k < n0; k++) if (ev.e[k].step >= start - barSteps && ev.e[k].step < start) { PEv c = ev.e[k]; c.step += barSteps; *pev_push(&ev) = c; }
      last = ev.n ? ev.n - 1 : -1; continue;
    }
    if (!strcmp(b, "_")) { last = -1; continue; }
    if (!strcmp(b, "=")) {
      if (last >= 0 && ev.e[last].step + ev.e[last].len == start) ev.e[last].len += barSteps;
      else err(eln, "= in %s needs a note sounding right up to the bar line.", where);
      continue;
    }
    int pos = start; char tmp[2048]; snprintf(tmp, sizeof tmp, "%s", b);
    int lastIsReal = last; /* `last` may point to a zero-note chord event not stored; emulate with lastTmp */
    PEv lastTmp; int lastTmpValid = 0; (void)lastIsReal;
    for (char *tok = strtok(tmp, " \t"); tok; tok = strtok(NULL, " \t")) {
      int L = strlen(tok), allDash = 1;
      for (int i = 0; i < L; i++) if (tok[i] != '-') allDash = 0;
      if (allDash) {
        if (last >= 0 && ev.e[last].step + ev.e[last].len == pos) ev.e[last].len += L;
        else if (lastTmpValid && lastTmp.step + lastTmp.len == pos) lastTmp.len += L;
        pos += L; continue;
      }
      if (tok[0] == '.') { int i = 0; while (tok[i] == '.') i++; int j = i; while (tok[j] == '-') j++;
        if (!tok[j]) { pos += j; last = -1; lastTmpValid = 0; continue; } }
      /* note token: ~? (\[..\] | NOTE(+NOTE)*) [!?]* -* [!?]* */
      { const char *p = tok; int glide = 0; if (*p == '~') { glide = 1; p++; }
        int notes[MAXN], nn = 0, ok = 1, chord = 0; char label[12] = {0}; const char *h0 = p;
        if (*p == '[') { const char *e = strchr(p, ']'); if (!e || e == p + 1) ok = 0; else {
            char sym[64]; int sl = e - p - 1; if (sl > 63) sl = 63; memcpy(sym, p + 1, sl); sym[sl] = 0; chord = 1;
            p = e + 1;
            /* validity of the rest checked below; chord resolution after */
            int k = chord_to_midis(sym, voice->center, notes);
            if (k < 0) nn = -1; else nn = k;
          } }
        else { int m, c = note_at(p, &m); if (!c) ok = 0; else { notes[nn++] = m; p += c;
            while (*p == '+') { int c2 = note_at(p + 1, &m); if (!c2) { ok = 0; break; } if (nn < MAXN) notes[nn++] = m; p += 1 + c2; } } }
        if (ok) {
          int hl = p - h0; snprintf(label, sizeof label, "%.*s", hl > 11 ? 11 : hl, h0);
          char marks[64]; int nm = 0, dashes = 0;
          while (*p == '!' || *p == '?') { if (nm < 63) marks[nm++] = *p; p++; }
          while (*p == '-') { dashes++; p++; }
          while (*p == '!' || *p == '?') { if (nm < 63) marks[nm++] = *p; p++; }
          if (*p) ok = 0;
          else {
            if (nn < 0) { err(eln, "Unknown chord \"%s\" in %s.", label, where); nn = 0; }
            PEv e = {0}; e.step = pos; e.len = 1 + dashes; e.n = nn; memcpy(e.notes, notes, nn * sizeof(int));
            e.vel = vel_from(marks, nm); e.glide = glide; snprintf(e.label, sizeof e.label, "%s", label);
            if (nn) { *pev_push(&ev) = e; last = ev.n - 1; lastTmpValid = 0; }
            else { last = -1; lastTmp = e; lastTmpValid = 1; }
            pos += e.len; (void)chord; continue;
          }
        } }
      if (!strcmp(tok, "%") || !strcmp(tok, "_") || !strcmp(tok, "=")) err(eln, "\"%s\" must be alone in its bar (%s).", tok, where);
      else err(eln, "Can't read \"%s\" in %s. Notes look like D5, F#4, Bb3, chords like [Dm] or C4+E4+G4.", tok, where);
    }
    int used = pos - start;
    if (used != barSteps) {
      char W[160]; snprintf(W, sizeof W, "%s", where); W[0] = toupper(W[0]);
      err(eln, "%s has %d steps; a bar here holds %d.", W, used, barSteps);
      for (int k = 0; k < ev.n; k++) if (ev.e[k].step >= start + barSteps) ev.e[k].len = 0;
      if (last >= 0 && ev.e[last].step + ev.e[last].len > start + barSteps && used > barSteps) { int nl = start + barSteps - ev.e[last].step; ev.e[last].len = nl < 1 ? 1 : nl; }
    }
  }
  PEvList out = {0};
  for (int k = 0; k < ev.n; k++) if (ev.e[k].len > 0) *pev_push(&out) = ev.e[k];
  free(ev.e); return out;
}

static PEvList parse_drum(RawVoice *rv, int barSteps, Voice *voice, const char *pname) {
  PEvList ev = {0};
  for (int bi = 0; bi < rv->n; bi++) {
    int start = bi * barSteps, eln = cur_errln_bars(rv, bi);
    char where[160]; snprintf(where, sizeof where, "bar %d of \"%s\" in pattern %s", bi + 1, voice->name, pname);
    char s[2048]; int n = 0; for (const char *c = rv->bars[bi]; *c && n < 2047; c++) if (!isspace((unsigned char)*c)) s[n++] = *c; s[n] = 0;
    if (!strcmp(s, "%")) {
      if (bi == 0) err(eln, "%% in %s has no previous bar to repeat.", where);
      int n0 = ev.n;
      for (int k = 0; k < n0; k++) if (ev.e[k].step >= start - barSteps && ev.e[k].step < start) { PEv c = ev.e[k]; c.step += barSteps; *pev_push(&ev) = c; }
      continue;
    }
    if (!strcmp(s, "_")) continue;
    int k = 0;
    for (char *c = s; *c; c++, k++) {
      if (k >= barSteps) continue;
      float v = -1; if (*c == 'x') v = .8f; else if (*c == 'X') v = 1.05f; else if (*c == 'o') v = .42f;
      else if (*c != '.' && *c != '-') err(eln, "Drum lanes use x X o and . - found \"%c\" in %s.", *c, where);
      if (v > 0) { PEv *e = pev_push(&ev); e->step = start + k; e->len = 1; e->vel = v; e->label[0] = *c; }
    }
    if (k != barSteps) { char W[160]; snprintf(W, sizeof W, "%s", where); W[0] = toupper(W[0]); err(eln, "%s has %d steps; a bar here holds %d.", W, k, barSteps); }
  }
  return ev;
}

/* ---------------------------------------------------------------- compile */
typedef struct {
  int ok; char name[40];
  /* resolved */
  RawVoice *raw[MAXV]; int order[MAXV], norder; int muted[MAXV];
  float tempo, swing; int beats, steps, has_tempo, has_beats, has_steps, has_swing; int ln;
  int resolving, resolved, compiled;
  /* compiled */
  int barSteps, bars; PEvList pv[MAXV]; int has[MAXV];
} CPat;
static CPat *cp;

static CPat *resolve(int pi) {
  CPat *r = &cp[pi]; Pattern *p = &song.pat[pi];
  if (r->resolved) return r;
  if (r->resolving) return NULL;
  r->resolving = 1;
  snprintf(r->name, 40, "%s", p->name); r->ln = p->ln;
  if (p->from[0]) {
    int bi = find_pat(p->from);
    CPat *base = NULL;
    if (bi >= 0 && cp[bi].resolving && !cp[bi].resolved) err(p->ln, "Pattern \"%s\" builds on itself through \"from\".", p->name);
    else if (bi < 0 || !(base = resolve(bi))) err(p->ln, "Pattern \"%s\" builds on \"%s\", which doesn't exist.", p->name, p->from);
    if (base) {
      memcpy(r->raw, base->raw, sizeof r->raw); memcpy(r->order, base->order, sizeof r->order); r->norder = base->norder;
      memcpy(r->muted, base->muted, sizeof r->muted);
      r->tempo = base->tempo; r->has_tempo = base->has_tempo; r->beats = base->beats; r->has_beats = base->has_beats;
      r->steps = base->steps; r->has_steps = base->has_steps; r->swing = base->swing; r->has_swing = base->has_swing;
    }
  }
  /* voice names not declared: keep -1 marker via negative index list */
  for (int k = 0; k < p->nv; k++) {
    int vi = find_voice(p->vnames[k]);
    if (vi < 0) { err(p->raw[k]->lns[0], "\"%s\" isn't a voice. Declare it first: voice %s INSTRUMENT", p->vnames[k], p->vnames[k]); continue; }
    r->raw[vi] = p->raw[k]; r->muted[vi] = 0;
    int in = 0; for (int j = 0; j < r->norder; j++) if (r->order[j] == vi) in = 1;
    if (!in) r->order[r->norder++] = vi;
  }
  for (int k = 0; k < p->nmute; k++) { int vi = find_voice(p->mute[k]); if (vi >= 0) r->muted[vi] = 1; }
  if (p->has_tempo) { r->tempo = p->tempo; r->has_tempo = 1; }
  if (p->has_beats) { r->beats = p->beats; r->has_beats = 1; }
  if (p->has_steps) { r->steps = p->steps; r->has_steps = 1; }
  if (p->has_swing) { r->swing = p->swing; r->has_swing = 1; }
  r->resolved = 1; r->ok = 1;
  return r;
}

static CPat *compile_pat(int pi) {
  CPat *r = resolve(pi);
  if (!r) return NULL;
  if (r->compiled) return r;
  if (!r->has_tempo) r->tempo = song.tempo;
  if (!r->has_beats) r->beats = song.beats;
  if (!r->has_steps) r->steps = song.steps;
  if (!r->has_swing) r->swing = song.swing;
  r->barSteps = r->beats * r->steps;
  int nb = 0;
  for (int k = 0; k < r->norder; k++) {
    int vi = r->order[k]; if (r->muted[vi]) continue;
    Voice *v = &song.v[vi];
    r->pv[vi] = v->drum ? parse_drum(r->raw[vi], r->barSteps, v, r->name) : parse_melodic(r->raw[vi], r->barSteps, v, r->name);
    r->has[vi] = 1;
    if (r->raw[vi]->n > nb) nb = r->raw[vi]->n;
  }
  if (!nb) err(r->ln, "Pattern \"%s\" has no music lines.", r->name);
  r->bars = nb ? nb : 1; r->compiled = 1;
  return r;
}

typedef struct { double t, d; int v; float vel; int nm; int m[MAXN]; int has_g; int g; } TEv;
typedef struct { int pat; int trans; double start, dur, stepDur, sw; int total, rep, times; } Sect;
typedef struct { TEv *e; int n, cap; Sect *s; int ns; double dur; } Timeline;
static int lastMidi[MAXV], hasLast[MAXV];
static int cmp_tev(const void *a, const void *b) { const TEv *x = a, *y = b; if (x->t < y->t) return -1; if (x->t > y->t) return 1; return x->v - y->v; }

static Timeline timeline(Ref *refs, int nrefs) {
  Timeline T = {0}; double t = 0;
  for (int ri = 0; ri < nrefs; ri++) {
    int pi = find_pat(refs[ri].name);
    CPat *p = pi >= 0 ? compile_pat(pi) : NULL;
    if (!p) { err(refs[ri].ln, "There's no pattern called \"%s\".", refs[ri].name); continue; }
    double stepDur = 60.0 / p->tempo / p->steps;
    double sw = (p->steps % 2 == 0) ? p->swing : 0;
    int total = p->bars * p->barSteps;
    #define TIMEOF(s) (((s) + (((s) % 2 == 1) ? sw : 0)) * stepDur)
    for (int rep = 0; rep < refs[ri].times; rep++) {
      T.s = realloc(T.s, (T.ns + 1) * sizeof(Sect));
      T.s[T.ns++] = (Sect){pi, refs[ri].trans, t, total * stepDur, stepDur, sw, total, rep, refs[ri].times};
      int first = T.n;
      for (int vi = 0; vi < song.nv; vi++) {
        if (!p->has[vi]) continue;
        Voice *voice = &song.v[vi];
        for (int k = 0; k < p->pv[vi].n; k++) {
          PEv *e = &p->pv[vi].e[k];
          if (e->step >= total) continue;
          double t0 = TIMEOF(e->step);
          int se = e->step + e->len; if (se > total) se = total;
          double d = TIMEOF(se) - t0;
          if (T.n == T.cap) { T.cap = T.cap ? T.cap * 2 : 256; T.e = realloc(T.e, T.cap * sizeof(TEv)); }
          TEv *ev = &T.e[T.n++]; memset(ev, 0, sizeof *ev);
          ev->t = t + t0; ev->d = d; ev->v = vi; ev->vel = e->vel;
          if (!voice->drum) {
            ev->nm = e->n; for (int j = 0; j < e->n; j++) ev->m[j] = e->notes[j] + voice->trans + refs[ri].trans;
            ev->d = fmax(0.02, d * voice->gate);
            if (e->glide && hasLast[vi]) { ev->has_g = 1; ev->g = lastMidi[vi]; }
          }
        }
      }
      qsort(T.e + first, T.n - first, sizeof(TEv), cmp_tev);
      for (int k = first; k < T.n; k++) if (T.e[k].nm) { lastMidi[T.e[k].v] = T.e[k].m[T.e[k].nm - 1]; hasLast[T.e[k].v] = 1; }
      t += total * stepDur;
    }
  }
  T.dur = t; return T;
}

static int cmp_err(const void *a, const void *b) { return ((Err *)a)->line - ((Err *)b)->line; }

static Timeline intro, loopT;
static void compile_song(char *text) {
  parse(text);
  cp = calloc(song.npat + 1, sizeof(CPat));
  Ref *pr = song.play, *lr = song.loop; int np = song.nplay, nl = song.nloop;
  Ref *auto_ = NULL;
  if (!np && !nl) { auto_ = calloc(song.npat + 1, sizeof(Ref)); for (int i = 0; i < song.npat; i++) { snprintf(auto_[i].name, 40, "%s", song.pat[i].name); auto_[i].times = 1; auto_[i].ln = song.pat[i].ln; } lr = auto_; nl = song.npat; }
  intro = timeline(pr, np);
  loopT = timeline(lr, nl);
  if (!intro.dur && !loopT.dur && !nerr) err(1, "Nothing to play yet. Add a pattern and a loop line.");
  if (nerr) qsort(errs, nerr, sizeof(Err), cmp_err);
}

/* ======================================================================
 *  AUDIO ENGINE: tiny Web-Audio-like per-note node graphs
 * ====================================================================== */
enum { P_SET, P_LIN, P_EXP, P_TGT };
#define MAXEV 10
typedef struct {
  float def; int n; struct { uint8_t ty; double t; float v, tau; } e[MAXEV];
  int mod[3], nmod;
  int i, tgt; float v, v0, target, coef; double t0;
} Param;
enum { N_GAIN, N_FILT, N_OSC, N_NOISE, N_BUF };
enum { F_LP, F_HP, F_BP, F_PEAK, F_LS, F_HS };
enum { W_SINE, W_SQUARE, W_SAW, W_TRI, W_ORGAN, W_PIPE, W_CLAR, W_OBOE, W_BASSOON, W_REED, W_HORN, NWAVES };
#define MAXIN 16
typedef struct {
  uint8_t type, ftype, wave; int in[MAXIN], nin; Param p[2];
  float q, gdb, b0, b1, b2, a1, a2, z1, z2, lastf;
  double phase, start, stop; const float *buf; int blen; double rate, pos; uint32_t rng;
  float out[BLK];
} Node;
#define MAXNODE 36
typedef struct Note { int used, ch; double end; int nn, order[MAXNODE], no; Node n[MAXNODE]; } Note;
#define MAXNOTES 384
static Note *notes; static Note *NB; /* note under construction */

static float wt[NWAVES][2048];
static float sintab[4097];
static void init_tables(void) {
  for (int i = 0; i <= 4096; i++) sintab[i] = sinf(2 * M_PI * i / 4096.0);
  static const float H[][13] = {
    [W_ORGAN] = {1, .8, .5, .42, 0, .25, 0, .2}, [W_PIPE] = {1, .55, .32, .4, .08, .18, 0, .2, 0, .07, 0, .06},
    [W_CLAR] = {1, .05, .72, .04, .45, .02, .26, 0, .12, 0, .06}, [W_OBOE] = {.5, 1, .85, .5, .36, .22, .15, .1, .06},
    [W_BASSOON] = {.45, 1, .78, .56, .42, .3, .22, .14, .1, .06}, [W_REED] = {1, .55, .45, .32, .3, .22, .18, .13, .11, .08, .06, .05},
    [W_HORN] = {1, .5, .3, .18, .1, .05}};
  for (int w = W_ORGAN; w < NWAVES; w++) {
    float pk = 0;
    for (int i = 0; i < 2048; i++) { double s = 0; for (int h = 0; h < 13; h++) s += H[w][h] * sin(2 * M_PI * (h + 1) * i / 2048.0); wt[w][i] = s; if (fabs(s) > pk) pk = fabs(s); }
    for (int i = 0; i < 2048; i++) wt[w][i] /= pk; /* PeriodicWave default normalisation */
  }
}

/* --- param automation (AudioParam semantics, stepped per sample) --- */
static void pins(Param *p, int ty, double t, float v, float tau) {
  if (p->n >= MAXEV) return;
  int k = p->n; while (k > 0 && p->e[k - 1].t > t) { p->e[k] = p->e[k - 1]; k--; }
  p->e[k].ty = ty; p->e[k].t = t; p->e[k].v = v; p->e[k].tau = tau; p->n++;
}
static inline float pnext(Param *p, double t) {
  for (;;) {
    if (p->i < p->n) {
      typeof(p->e[0]) *e = &p->e[p->i];
      if (e->ty == P_LIN || e->ty == P_EXP) {
        if (t >= e->t) { p->v = e->v; p->v0 = e->v; p->t0 = e->t; p->tgt = 0; p->i++; continue; }
        double span = e->t - p->t0, fr = span > 0 ? (t - p->t0) / span : 1; if (fr < 0) fr = 0;
        if (e->ty == P_LIN) p->v = p->v0 + (e->v - p->v0) * fr;
        else p->v = (p->v0 > 0 && e->v > 0) ? p->v0 * powf(e->v / p->v0, fr) : p->v0;
        return p->v;
      }
      if (t >= e->t) {
        if (e->ty == P_SET) { p->v = e->v; p->tgt = 0; }
        else { p->tgt = 1; p->target = e->v; p->coef = expf(-1.0f / (e->tau * SR)); }
        p->v0 = p->v; p->t0 = e->t; p->i++; continue;
      }
    }
    if (p->tgt) { p->v = p->target + (p->v - p->target) * p->coef; p->v0 = p->v; p->t0 = t; }
    return p->v;
  }
}

/* --- graph construction API (mirrors the JS helpers) --- */
static int newnode(int type) {
  if (NB->nn >= MAXNODE) return -1;
  Node *n = &NB->n[NB->nn]; memset(n, 0, sizeof *n - sizeof n->out);
  n->type = type; n->p[0].def = n->p[0].v = 0; n->rng = (uint32_t)rand() | 1;
  n->start = 0; n->stop = 1e30;
  return NB->nn++;
}
static Param *PRM(int node, int which) { static Param dummy; if (node < 0) { memset(&dummy, 0, sizeof dummy); return &dummy; } return &NB->n[node].p[which]; }
static void C(int a, int b) { if (a < 0 || b < 0) return; Node *n = &NB->n[b]; if (n->nin < MAXIN) n->in[n->nin++] = a; }
static void CP(int a, int b, int which) { if (a < 0 || b < 0) return; Param *p = &NB->n[b].p[which]; if (p->nmod < 3) p->mod[p->nmod++] = a; }
static int G(float v) { int k = newnode(N_GAIN); if (k >= 0) NB->n[k].p[0].def = NB->n[k].p[0].v = v; return k; }
static void setf(int k, float f) { NB->n[k].p[0].def = NB->n[k].p[0].v = clampf(f, 10, NYQ * .95f); }
static int F(int ty, float f, float q, float gdb) {
  int k = newnode(N_FILT); if (k < 0) return k;
  Node *n = &NB->n[k]; n->ftype = ty; n->q = q; n->gdb = gdb; setf(k, f); n->lastf = -1; return k;
}
typedef struct { double from; float glide, bright, att, rel; } P;
static void notestop(double s) { if (s > NB->end) NB->end = s; }
static int O(int wave, double f, double t, double stop, const P *p, double ratio, float det) {
  int k = newnode(N_OSC); if (k < 0) return k;
  Node *n = &NB->n[k]; n->wave = wave; n->start = t; n->stop = stop; notestop(stop);
  double ff = clampf(f * ratio, 1, NYQ * .98);
  n->p[0].def = n->p[0].v = ff;
  if (p && p->from > 0) { pins(&n->p[0], P_SET, t, clampf(p->from * ratio, 1, NYQ * .98), 0); pins(&n->p[0], P_EXP, t + p->glide, ff, 0); }
  else pins(&n->p[0], P_SET, t, ff, 0);
  n->p[1].def = n->p[1].v = det;
  return k;
}
static double adsr(Param *pr, double t, double d, float a, float dc, float s, float r, float peak) {
  double tOn = t + a, tOff = fmax(t + d, tOn + .003);
  pins(pr, P_SET, t, 0, 0); pins(pr, P_LIN, tOn, peak, 0);
  if (s < 1) pins(pr, P_TGT, tOn, peak * s, fmaxf(.002f, dc / 3));
  pins(pr, P_TGT, tOff, 0, fmaxf(.002f, r / 4));
  return tOff + r * 1.8 + .03;
}
static double perc(Param *pr, double t, float a, float tau, float peak, double damp, float dampTau) {
  pins(pr, P_SET, t, 0, 0); pins(pr, P_LIN, t + a, peak, 0);
  pins(pr, P_TGT, t + a, 0, fmaxf(.002f, tau));
  double end = t + a + tau * 7;
  if (damp > 0 && damp + dampTau * 7 < end) { double td = fmax(damp, t + a + .002); pins(pr, P_TGT, td, 0, dampTau); end = td + dampTau * 7; }
  return end;
}
typedef struct { int type; float a, tau, peak; double damp; float dampTau, bend, bendTau; } PO;
static double partial(int out, double t, double f, PO o) {
  if (f >= NYQ * .9) return t;
  if (!o.dampTau) o.dampTau = .06f;
  int g = G(0); C(g, out);
  double end = perc(PRM(g, 0), t, o.a ? o.a : .002f, o.tau ? o.tau : .3f, o.peak, o.damp, o.dampTau);
  int os = O(o.type, f, t, end, NULL, 1, 0);
  if (os >= 0 && o.bend) { pins(PRM(os, 0), P_SET, t, f * o.bend, 0); pins(PRM(os, 0), P_TGT, t, f, o.bendTau ? o.bendTau : .02f); }
  C(os, g); return end;
}
typedef struct { int type; float f, q, a, tau, peak; } NO;
static void noise(int out, double t, NO o) {
  if (!o.f) o.f = 2000; if (!o.q) o.q = 1; if (!o.a) o.a = .001f; if (!o.tau) o.tau = .01f;
  int src = newnode(N_NOISE); if (src < 0) return;
  NB->n[src].start = t; NB->n[src].stop = t + o.a + o.tau * 7 + .01; notestop(NB->n[src].stop);
  int fl = F(o.type, o.f, o.q, 0), g = G(0);
  pins(PRM(g, 0), P_SET, t, 0, 0); pins(PRM(g, 0), P_LIN, t + o.a, o.peak, 0); pins(PRM(g, 0), P_TGT, t + o.a, 0, fmaxf(.001f, o.tau));
  C(src, fl); C(fl, g); C(g, out);
}
#define NOISE(out, t, ...) noise(out, t, (NO){.type = F_BP, __VA_ARGS__})
#define PART(out, t, f, ...) partial(out, t, f, (PO){.type = W_SINE, __VA_ARGS__})
static int noiseSrc(double t, double stop) { int k = newnode(N_NOISE); if (k < 0) return k; NB->n[k].start = t; NB->n[k].stop = stop; notestop(stop); return k; }
static void vibrato(double t, double stop, int *targets, int nt, float rate, float depth, float delay, float rise) {
  int lfo = O(W_SINE, rate * (.94 + frand() * .12), t, stop, NULL, 1, 0);
  int g = G(0);
  pins(PRM(g, 0), P_SET, t, 0, 0); pins(PRM(g, 0), P_SET, t + delay, 0, 0); pins(PRM(g, 0), P_LIN, t + delay + rise, depth, 0);
  C(lfo, g);
  for (int i = 0; i < nt; i++) CP(g, targets[i], 1);
}
static int metal(int out, double t, double stop, float mult) {
  int sum = G(.16f); C(sum, out);
  static const float fs[] = {205.3f, 304.4f, 369.6f, 522.7f, 540, 800};
  for (int i = 0; i < 6; i++) C(O(W_SQUARE, fs[i] * mult, t, stop, NULL, 1, 0), sum);
  return sum;
}

/* --- Karplus-Strong plucked strings (precomputed buffers, cached) --- */
typedef struct { int id; float b, decay, color, dur, hang, dampTau; } KS;
enum { K_HARP, K_GTR, K_BANJO, K_HPSI, K_PIZZ, K_UPR };
static const KS PLUCK[] = {
  {K_HARP, .45f, .9985f, .55f, 2.8f, 1.4f, .25f}, {K_GTR, .38f, .997f, .4f, 1.9f, .2f, .06f},
  {K_BANJO, .18f, .988f, .05f, 1.1f, .1f, .05f}, {K_HPSI, .14f, .994f, 0, 1.6f, .12f, .05f},
  {K_PIZZ, .5f, .982f, .6f, .8f, .15f, .05f}, {K_UPR, .5f, .996f, .7f, 1.7f, .04f, .07f}};
typedef struct { int id, N, len; float *y; double f0; } KSBuf;
static KSBuf kscache[512]; static int nks;
static KSBuf *ks(double f, const KS *c) {
  int N = (int)floor(SR / f - c->b); if (N < 2) N = 2;
  for (int i = 0; i < nks; i++) if (kscache[i].id == c->id && kscache[i].N == N) return &kscache[i];
  if (nks == 512) { for (int i = 0; i < nks; i++) free(kscache[i].y); nks = 0; }
  KSBuf *e = &kscache[nks++];
  int len = (int)(SR * c->dur); float *y = calloc(len, sizeof(float));
  double lp = 0, mean = 0, pk = 1e-6;
  for (int i = 0; i < N && i < len; i++) { lp += (1 - c->color) * ((frand() * 2 - 1) - lp); y[i] = lp; mean += lp; }
  mean /= N;
  for (int i = 0; i < N && i < len; i++) { y[i] -= mean; if (fabs(y[i]) > pk) pk = fabs(y[i]); }
  for (int i = 0; i < N && i < len; i++) y[i] /= pk;
  for (int i = N; i < len; i++) y[i] = c->decay * ((1 - c->b) * y[i - N] + c->b * (i - N - 1 >= 0 ? y[i - N - 1] : 0));
  int fade = len / 4;
  for (int i = 0; i < fade; i++) { float k = (float)i / fade; y[len - fade + i] *= (1 - k) * (1 - k); }
  e->id = c->id; e->N = N; e->len = len; e->y = y; e->f0 = (double)SR / (N + c->b);
  return e;
}
static void pluck(int out, double t, double d, double f, float v, const KS *c, int *chain, int nc) {
  KSBuf *e = ks(f, c);
  int src = newnode(N_BUF); if (src < 0) return;
  Node *n = &NB->n[src]; n->buf = e->y; n->blen = e->len; n->rate = f / e->f0; n->start = t; n->pos = 0;
  int g = G(0);
  double end = perc(PRM(g, 0), t, .001f, 50, v, t + d + c->hang, c->dampTau);
  NB->n[src].stop = fmin(end, t + e->len / (double)SR / NB->n[src].rate); notestop(NB->n[src].stop);
  int node = src;
  for (int i = 0; i < nc; i++) { C(node, chain[i]); node = chain[i]; }
  C(node, g); C(g, out);
}

/* --- instruments: play(out, t, dur, freq, vel, p) --- */
#define ARGS int out, double t, double d, double f, float v, P *p
#define ATT(x) (p->att ? p->att : (x))
#define REL(x) (p->rel ? p->rel : (x))
#define A2(...) (int[]){__VA_ARGS__}
static void choirVoice(ARGS, const float fm[3][3]) {
  int g = G(0); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.28f), .3f, .95f, REL(.6f), v * 1.6f);
  int src = G(1), os[2]; float cs[2] = {-7, 6};
  for (int i = 0; i < 2; i++) { os[i] = O(W_SAW, f, t, end, p, 1, cs[i]); int og = G(.5f); C(os[i], og); C(og, src); }
  vibrato(t, end, os, 2, 5.1f, 12, .2f, .5f);
  for (int i = 0; i < 3; i++) { int bp = F(F_BP, fm[i][0] * (p->bright > 1 ? 1.1f : 1), fm[i][1], 0); int fg = G(fm[i][2]); C(src, bp); C(bp, fg); C(fg, g); }
  int n = noiseSrc(t, end), nb = F(F_BP, fm[1][0], 2, 0), ng = G(v * .04f); C(n, nb); C(nb, ng); C(ng, g);
}
static void i_steeldrum(ARGS) {
  float tau = clampf(.5f * powf(440 / f, .45f), .15f, 1.1f);
  int lp = F(F_LP, 5200 * p->bright, .5f, 0); C(lp, out);
  double damp = t + d + .9;
  static const float R[5][4] = {{1, 1, 1, .002f}, {1.0035f, .32f, 1.1f, .002f}, {2, .52f, .55f, .016f}, {3, .17f, .32f, .004f}, {4.07f, .06f, .18f, .002f}};
  for (int i = 0; i < 5; i++) PART(lp, t, f * R[i][0], .a = R[i][3], .tau = tau * R[i][2], .peak = v * R[i][1] * .5f, .damp = damp);
  NOISE(lp, t, .f = 2600, .q = .8f, .tau = .006f, .peak = v * .05f);
}
static void i_marimba(ARGS) {
  float tau = clampf(.26f * sqrtf(330 / f), .08f, .6f);
  PART(out, t, f, .a = .002f, .tau = tau, .peak = v * .8f);
  PART(out, t, f * 3.98, .a = .001f, .tau = tau * .18f, .peak = v * .22f * p->bright);
  PART(out, t, f * 9.9, .a = .001f, .tau = tau * .05f, .peak = v * .05f * p->bright);
  NOISE(out, t, .f = f * 2.5f, .q = 1.2f, .tau = .004f, .peak = v * .06f);
}
static void i_vibes(ARGS) {
  int trem = G(.82f); C(trem, out);
  float tau = clampf(1.1f * powf(440 / f, .3f), .4f, 1.8f);
  double end = t + fmin(tau * 7, d + 2.2);
  int lfo = O(W_SINE, 5.2, t, end, NULL, 1, 0); int lg = G(.18f); C(lfo, lg); CP(lg, trem, 0);
  PART(trem, t, f, .a = .002f, .tau = tau, .peak = v * .7f, .damp = t + d + 1.2, .dampTau = .2f);
  PART(trem, t, f * 4, .a = .001f, .tau = .18f, .peak = v * .14f * p->bright);
  NOISE(trem, t, .f = f * 3, .q = 1, .tau = .004f, .peak = v * .03f);
}
static void i_celesta(ARGS) {
  float tau = clampf(.55f * powf(440 / f, .3f), .2f, .9f);
  PART(out, t, f, .a = .002f, .tau = tau, .peak = v * .7f);
  PART(out, t, f * 2, .a = .001f, .tau = tau * .4f, .peak = v * .14f);
  PART(out, t, f * 4.02, .a = .001f, .tau = tau * .12f, .peak = v * .1f * p->bright);
  NOISE(out, t, .f = 5000, .q = 1, .tau = .003f, .peak = v * .04f);
}
static void i_glock(ARGS) {
  PART(out, t, f, .a = .001f, .tau = .7f, .peak = v * .6f);
  PART(out, t, f * 2.76, .a = .001f, .tau = .22f, .peak = v * .25f * p->bright);
  PART(out, t, f * 5.4, .a = .001f, .tau = .07f, .peak = v * .14f * p->bright);
  PART(out, t, f * 8.93, .a = .001f, .tau = .03f, .peak = v * .06f * p->bright);
}
static void i_xylophone(ARGS) {
  float tau = clampf(.13f * sqrtf(440 / f), .05f, .25f);
  PART(out, t, f, .a = .001f, .tau = tau, .peak = v * .75f);
  PART(out, t, f * 3, .a = .001f, .tau = tau * .4f, .peak = v * .35f * p->bright);
  PART(out, t, f * 6, .a = .001f, .tau = tau * .15f, .peak = v * .1f * p->bright);
  NOISE(out, t, .f = 4000, .q = 1, .tau = .004f, .peak = v * .1f);
}
static void i_musicbox(ARGS) {
  PART(out, t, f, .a = .001f, .tau = .5f, .peak = v * .7f);
  PART(out, t, f * 3, .a = .001f, .tau = .12f, .peak = v * .12f);
  PART(out, t, f * 5.2, .a = .001f, .tau = .05f, .peak = v * .06f * p->bright);
  NOISE(out, t, .f = 7000, .q = 2, .tau = .002f, .peak = v * .05f);
}
static void i_bell(ARGS) {
  double damp = t + d + 3;
  static const float R[8][3] = {{.5f, .35f, 3.5f}, {1, 1, 2.4f}, {1.19f, .55f, 1.7f}, {1.5f, .38f, 1.4f}, {2, .45f, 1.1f}, {2.52f, .22f, .8f}, {3.01f, .16f, .55f}, {4.1f, .08f, .35f}};
  for (int i = 0; i < 8; i++) PART(out, t, f * R[i][0], .a = .002f, .tau = R[i][2], .peak = v * R[i][1] * .35f, .damp = damp, .dampTau = .4f);
  NOISE(out, t, .f = f * 4, .q = 1, .tau = .01f, .peak = v * .05f);
}
static void i_organ(ARGS) {
  int g = G(0), lp = F(F_LP, 5500 * p->bright, .5f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.005f), .1f, 1, REL(.06f), v * .5f);
  int o = O(W_ORGAN, f, t, end, p, 1, 0); C(o, lp);
  vibrato(t, end, A2(o), 1, 6.3f, 5, 0, .05f);
  noise(out, t, (NO){.type = F_LP, .f = 2500, .q = .5f, .tau = .002f, .peak = v * .1f});
}
static void i_pipe(ARGS) {
  int g = G(0), lp = F(F_LP, 4200 * p->bright, .5f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.06f), .1f, 1, REL(.28f), v * .38f);
  C(O(W_PIPE, f, t, end, p, 1, 0), lp);
  int sub = G(.45f); C(sub, lp); C(O(W_SINE, f, t, end, p, .5, 0), sub);
  NOISE(out, t, .f = f * 3, .q = 2, .a = .01f, .tau = .02f, .peak = v * .04f);
}
static void i_strings(ARGS) {
  int g = G(0), lp = F(F_LP, fminf(9000, (1300 + f * 2.6f) * p->bright), .6f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.16f), .3f, .9f, REL(.38f), v * .5f);
  int os[3]; float cs[3] = {-8, 0, 8};
  for (int i = 0; i < 3; i++) { os[i] = O(W_SAW, f, t, end, p, 1, cs[i]); int og = G(.22f); C(os[i], og); C(og, lp); }
  vibrato(t, end, os, 3, 5.3f, 7, .15f, .4f);
}
static void i_pad(ARGS) {
  int g = G(0), lp = F(F_LP, (600 + f * 1.4f) * p->bright, .9f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.5f), .1f, 1, REL(1.0f), v * .45f);
  float cs[3] = {-12, 0, 11};
  for (int i = 0; i < 3; i++) { int og = G(.24f); C(O(W_SAW, f, t, end, p, 1, cs[i]), og); C(og, lp); }
}
static void i_choir(ARGS) { static const float fm[3][3] = {{730, 7, 1}, {1090, 8, .55f}, {2440, 10, .25f}}; choirVoice(out, t, d, f, v, p, fm); }
static void i_voices(ARGS) { static const float fm[3][3] = {{380, 6, 1}, {820, 8, .35f}, {2500, 10, .1f}}; choirVoice(out, t, d, f, v, p, fm); }
static void i_brass(ARGS) {
  int g = G(0), lp = F(F_LP, f, 1.3f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.03f), .2f, .85f, REL(.12f), v * .42f);
  float pk = fminf(11000, (f * 5 + 700) * p->bright * (.55f + .45f * v));
  Param *fp = PRM(lp, 0); pins(fp, P_SET, t, f * 1.1, 0); pins(fp, P_LIN, t + .06, pk, 0); pins(fp, P_TGT, t + .06, f * 1.2 + (pk - f) * .5, .2f);
  int os[2]; float cs[2] = {-5, 5};
  for (int i = 0; i < 2; i++) { os[i] = O(W_SAW, f, t, end, p, 1, cs[i]); C(os[i], lp); }
  vibrato(t, end, os, 2, 5.2f, 6, .35f, .3f);
}
static void i_trumpet(ARGS) {
  int g = G(0), lp = F(F_LP, f, 1.6f, 0), pk2 = F(F_PEAK, 1400, 1, 5); C(lp, pk2); C(pk2, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.02f), .15f, .8f, REL(.09f), v * .4f);
  float pk = fminf(12000, (f * 7 + 900) * p->bright * (.5f + .5f * v));
  Param *fp = PRM(lp, 0); pins(fp, P_SET, t, f * 1.5, 0); pins(fp, P_LIN, t + .04, pk, 0); pins(fp, P_TGT, t + .04, f * 2 + (pk - f) * .45, .15f);
  int o = O(W_SAW, f, t, end, p, 1, 0); C(o, lp);
  vibrato(t, end, A2(o), 1, 5.6f, 11, .25f, .25f);
}
static void i_horn(ARGS) {
  int g = G(0), lp = F(F_LP, f * 2, .8f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.06f), .3f, .9f, REL(.2f), v * .5f);
  Param *fp = PRM(lp, 0); pins(fp, P_SET, t, f * 1.2, 0); pins(fp, P_LIN, t + .08, fminf(6000, (f * 3 + 300) * p->bright), 0);
  int o1 = O(W_SAW, f, t, end, p, 1, 0), g1 = G(.5f); C(o1, g1); C(g1, lp);
  int o2 = O(W_HORN, f, t, end, p, 1, 4); C(o2, lp);
  vibrato(t, end, A2(o1, o2), 2, 4.8f, 5, .4f, .4f);
}
static void i_tuba(ARGS) {
  int g = G(0), lp = F(F_LP, (f * 3 + 150) * p->bright, 1.0f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.035f), .2f, .8f, REL(.1f), v * .55f);
  C(O(W_SAW, f, t, end, p, 1, 0), lp);
  int sg = G(.5f); C(O(W_SINE, f, t, end, p, 1, 0), sg); C(sg, lp);
}
static void i_flute(ARGS) {
  int g = G(0); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.055f), .15f, .85f, REL(.09f), v * .48f);
  int o1 = O(W_SINE, f, t, end, p, 1, 0), g1 = G(.75f); C(o1, g1); C(g1, g);
  int o2 = O(W_TRI, f, t, end, p, 1, 0), g2 = G(.22f * p->bright); C(o2, g2); C(g2, g);
  int o3 = O(W_SINE, f, t, end, p, 2, 0), g3 = G(.07f); C(o3, g3); C(g3, g);
  vibrato(t, end, A2(o1, o2, o3), 3, 5, 13, .22f, .35f);
  int n = noiseSrc(t, end), hp = F(F_BP, fmin(f * 2.2, 9000), .7f, 0), ng = G(0);
  Param *q = PRM(ng, 0); pins(q, P_SET, t, 0, 0); pins(q, P_LIN, t + .03, v * .05f, 0);
  pins(q, P_TGT, t + .03, v * .012f, .06f); pins(q, P_TGT, fmax(t + d, t + .04), 0, .03f);
  C(n, hp); C(hp, ng); C(ng, out);
}
static void i_reedish(ARGS, int wave, float lpf, float lpmax, float q, float a, float dc, float s, float r, float pk, float vr, float vd, float vdl, float vri) {
  int g = G(0), lp = F(F_LP, fminf(lpmax, lpf * p->bright), q, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(a), dc, s, REL(r), v * pk);
  int o = O(wave, f, t, end, p, 1, 0); C(o, lp);
  vibrato(t, end, A2(o), 1, vr, vd, vdl, vri);
}
static void i_clarinet(ARGS) { i_reedish(out, t, d, f, v, p, W_CLAR, 3000, 9000, .6f, .035f, .2f, .9f, .08f, .42f, 4.6f, 5, .4f, .4f); NOISE(out, t, .f = f * 3, .q = 1, .a = .01f, .tau = .02f, .peak = v * .02f); }
static void i_oboe(ARGS) { i_reedish(out, t, d, f, v, p, W_OBOE, 3800, 9000, .6f, .03f, .2f, .9f, .08f, .36f, 5.5f, 8, .25f, .3f); }
static void i_bassoon(ARGS) { i_reedish(out, t, d, f, v, p, W_BASSOON, 1700, 6000, .7f, .04f, .2f, .85f, .08f, .45f, 5, 5, .35f, .3f); }
static void i_accordion(ARGS) {
  int g = G(0), lp = F(F_LP, fminf(9000, (2600 + f) * p->bright), .7f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.025f), .2f, .92f, REL(.07f), v * .4f);
  float cs[3] = {0, 15, -13};
  for (int i = 0; i < 3; i++) { int og = G(i ? .28f : .36f); C(O(W_REED, f, t, end, p, 1, cs[i]), og); C(og, lp); }
}
static void i_fiddle(ARGS) {
  int g = G(0), body = F(F_PEAK, 2800, 1.2f, 6), body2 = F(F_PEAK, 480, 1.5f, 4), lp = F(F_LP, 6500 * p->bright, .6f, 0);
  C(body, body2); C(body2, lp); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.06f), .2f, .9f, REL(.14f), v * .3f);
  int os[2]; float cs[2] = {-4, 4};
  for (int i = 0; i < 2; i++) { os[i] = O(W_SAW, f, t, end, p, 1, cs[i]); C(os[i], body); }
  vibrato(t, end, os, 2, 5.8f, 14, .18f, .25f);
  noise(out, t, (NO){.type = F_HP, .f = 3000, .q = .5f, .a = .01f, .tau = .03f, .peak = v * .03f});
}
static void i_harp(ARGS) { pluck(out, t, d, f, v * .55f, &PLUCK[K_HARP], A2(F(F_LP, 3500 * p->bright, .5f, 0)), 1); PART(out, t, f, .a = .003f, .tau = .9f, .peak = v * .12f); }
static void i_guitar(ARGS) { pluck(out, t, d, f, v * .55f, &PLUCK[K_GTR], A2(F(F_LP, 4200 * p->bright, .5f, 0), F(F_PEAK, 220, 1, 3)), 2); }
static void i_banjo(ARGS) { pluck(out, t, d, f, v * .5f, &PLUCK[K_BANJO], A2(F(F_HP, 250, .5f, 0), F(F_PEAK, 2500, 1.5f, 5)), 2); }
static void i_harpsichord(ARGS) {
  pluck(out, t, d, f, v * .42f, &PLUCK[K_HPSI], A2(F(F_HP, 180, .5f, 0)), 1);
  pluck(out, t, d, f * 2, v * .16f * p->bright, &PLUCK[K_HPSI], A2(F(F_HP, 400, .5f, 0)), 1);
}
static void i_pizz(ARGS) { pluck(out, t, d, f, v * .6f, &PLUCK[K_PIZZ], A2(F(F_LP, 2400 * p->bright, .6f, 0)), 1); PART(out, t, f, .a = .002f, .tau = .12f, .peak = v * .18f); }
static void i_upright(ARGS) {
  pluck(out, t, d, f, v * .5f, &PLUCK[K_UPR], A2(F(F_LP, 1400 * p->bright, .6f, 0)), 1);
  PART(out, t, f, .a = .004f, .tau = .5f, .peak = v * .45f, .damp = t + d + .04, .dampTau = .07f);
  noise(out, t, (NO){.type = F_LP, .f = 900, .q = .5f, .tau = .01f, .peak = v * .12f});
}
static void i_fretless(ARGS) {
  int g = G(0), lp = F(F_LP, 300, 3.2f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.012f), .6f, .72f, REL(.08f), v * .6f);
  float top = fminf(4000, (f * 4.5f + 250) * p->bright);
  Param *fp = PRM(lp, 0); pins(fp, P_SET, t, f * 1.2 + 80, 0); pins(fp, P_LIN, t + .07, top, 0); pins(fp, P_TGT, t + .07, f * 2.2 + 150, .25f);
  int o1 = O(W_SAW, f, t, end, p, 1, 0), g1 = G(.38f); C(o1, g1); C(g1, lp);
  int o2 = O(W_SINE, f, t, end, p, 1, 0), g2 = G(.75f); C(o2, g2); C(g2, lp);
  vibrato(t, end, A2(o1, o2), 2, 4.5f, 6, .3f, .4f);
}
static void i_synbass(ARGS) {
  int g = G(0), lp = F(F_LP, 300, 5, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.003f), .35f, .55f, REL(.06f), v * .5f);
  Param *fp = PRM(lp, 0); pins(fp, P_SET, t, fminf(5000, 2600 * p->bright * v), 0); pins(fp, P_TGT, t, f * 2 + 80, .07f);
  C(O(W_SAW, f, t, end, p, 1, 0), lp);
  int sq = G(.5f); C(O(W_SQUARE, f, t, end, p, 1, -6), sq); C(sq, lp);
}
static void i_timpani(ARGS) {
  double damp = t + fmax(d, .15) + .5;
  PART(out, t, f, .a = .004f, .tau = .55f, .peak = v * .85f, .bend = 1.035f, .bendTau = .05f, .damp = damp, .dampTau = .15f);
  PART(out, t, f * 1.505, .a = .003f, .tau = .35f, .peak = v * .32f, .damp = damp, .dampTau = .15f);
  PART(out, t, f * 1.99, .a = .003f, .tau = .25f, .peak = v * .2f, .damp = damp, .dampTau = .15f);
  PART(out, t, f * 2.44, .a = .002f, .tau = .15f, .peak = v * .1f);
  noise(out, t, (NO){.type = F_LP, .f = 500, .q = .7f, .tau = .03f, .peak = v * .5f});
}
static void i_chip(ARGS) {
  int g = G(0), lp = F(F_LP, 6000 * p->bright, .5f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.003f), .1f, .8f, REL(.04f), v * .3f);
  int o = O(W_SQUARE, f, t, end, p, 1, 0); C(o, lp);
  vibrato(t, end, A2(o), 1, 6, 12, .25f, .1f);
}
static void i_basic(ARGS, int w) {
  int g = G(0), lp = F(F_LP, 8000 * p->bright, .5f, 0); C(lp, g); C(g, out);
  double end = adsr(PRM(g, 0), t, d, ATT(.008f), .2f, .85f, REL(.08f), v * .4f);
  C(O(w, f, t, end, p, 1, 0), lp);
}
static void i_sine(ARGS) { i_basic(out, t, d, f, v, p, W_SINE); }
static void i_square(ARGS) { i_basic(out, t, d, f, v, p, W_SQUARE); }
static void i_saw(ARGS) { i_basic(out, t, d, f, v, p, W_SAW); }
static void i_triangle(ARGS) { i_basic(out, t, d, f, v, p, W_TRI); }

typedef void (*PlayFn)(ARGS);
static const struct { PlayFn fn; float rev, level; } INST[] = { /* same order as MELODIC[] */
  {i_steeldrum, .22f, .66f}, {i_marimba, .18f, .5f}, {i_vibes, .35f, .4f}, {i_celesta, .35f, .63f}, {i_glock, .35f, .53f},
  {i_xylophone, .2f, .72f}, {i_musicbox, .4f, .64f}, {i_bell, .45f, .71f}, {i_organ, .15f, .98f}, {i_pipe, .55f, 1.01f},
  {i_strings, .4f, 3.18f}, {i_pad, .5f, 2.18f}, {i_choir, .5f, 2.02f}, {i_voices, .5f, 2.01f}, {i_brass, .25f, .83f},
  {i_trumpet, .25f, 1.17f}, {i_horn, .4f, .7f}, {i_tuba, .2f, .7f}, {i_flute, .38f, 1.0f}, {i_clarinet, .3f, 1.16f},
  {i_oboe, .3f, 1.98f}, {i_bassoon, .25f, 1.72f}, {i_accordion, .22f, 2.06f}, {i_fiddle, .3f, .93f}, {i_harp, .45f, 1.07f},
  {i_guitar, .25f, 1.53f}, {i_banjo, .18f, 1.18f}, {i_harpsichord, .3f, 1.74f}, {i_pizz, .35f, 1.21f}, {i_upright, .15f, .72f},
  {i_fretless, .12f, .69f}, {i_synbass, .08f, .76f}, {i_timpani, .45f, .53f}, {i_chip, .15f, 1.17f},
  {i_sine, .2f, .94f}, {i_square, .2f, .78f}, {i_saw, .2f, 1.35f}, {i_triangle, .2f, 1.15f}};

/* --- drums: hit(out, t, vel) --- */
#define DARGS int out, double t, float v
static void cymbal(DARGS, float tau, float hpf, float pk) {
  int g = G(0), hp = F(F_HP, hpf, .6f, 0), pkf = F(F_PEAK, 10000, 1, 4); C(hp, pkf); C(pkf, g); C(g, out);
  double end = perc(PRM(g, 0), t, .001f, tau, v * pk, 0, .06f);
  int n = noiseSrc(t, end); C(n, hp);
  metal(hp, t, end, 1.0f);
}
static void hand(DARGS, float f, float tau) {
  int slap = v > .95f;
  PART(out, t, f, .a = .002f, .tau = slap ? tau * .6f : tau, .peak = v * .8f, .bend = 1.12f, .bendTau = .012f);
  PART(out, t, f * 1.52, .a = .001f, .tau = tau * .3f, .peak = v * .15f);
  NOISE(out, t, .f = slap ? 2600 : 1600, .q = 1, .tau = slap ? .02f : .008f, .peak = v * (slap ? .5f : .18f));
}
static void tom(DARGS, float f) {
  PART(out, t, f, .a = .002f, .tau = .2f, .peak = v * .85f, .bend = 1.55f, .bendTau = .025f);
  PART(out, t, f * 1.6, .a = .001f, .tau = .06f, .peak = v * .15f);
  noise(out, t, (NO){.type = F_LP, .f = 1600, .q = .5f, .tau = .02f, .peak = v * .2f});
}
static void d_kick(DARGS) {
  int g = G(0); C(g, out);
  double end = perc(PRM(g, 0), t, .003f, .13f, v, 0, .06f);
  int o = O(W_SINE, 150, t, end, NULL, 1, 0); pins(PRM(o, 0), P_EXP, t + .11, 46, 0); C(o, g);
  noise(out, t, (NO){.type = F_LP, .f = 3000, .q = .5f, .tau = .003f, .peak = v * .28f});
}
static void d_snare(DARGS) {
  noise(out, t, (NO){.type = F_HP, .f = 1100, .q = .5f, .tau = .055f, .peak = v * .6f});
  NOISE(out, t, .f = 4500, .q = .8f, .tau = .03f, .peak = v * .25f);
  partial(out, t, 185, (PO){.type = W_TRI, .a = .001f, .tau = .035f, .peak = v * .5f, .bend = 1.25f, .bendTau = .02f});
}
static void d_rim(DARGS) { PART(out, t, 1650, .a = .001f, .tau = .007f, .peak = v * .5f); PART(out, t, 520, .a = .001f, .tau = .016f, .peak = v * .4f); NOISE(out, t, .f = 3200, .q = 2, .tau = .008f, .peak = v * .55f); }
static void d_hat(DARGS) { cymbal(out, t, v, .02f, 7500, .5f); }
static void d_ohat(DARGS) { cymbal(out, t, v, .13f, 7000, .45f); }
static void d_ride(DARGS) {
  int g = G(0), bp = F(F_BP, 5500, .8f, 0); C(bp, g); C(g, out);
  double end = perc(PRM(g, 0), t, .001f, .38f, v * .5f, 0, .06f);
  metal(bp, t, end, 1.5f);
  noise(out, t, (NO){.type = F_HP, .f = 8000, .q = .5f, .tau = .2f, .peak = v * .07f});
}
static void d_crash(DARGS) {
  noise(out, t, (NO){.type = F_HP, .f = 3500, .q = .5f, .a = .002f, .tau = .55f, .peak = v * .4f});
  int g = G(0), bp = F(F_BP, 4500, .7f, 0); C(bp, g); C(g, out);
  double end = perc(PRM(g, 0), t, .002f, .45f, v * .35f, 0, .06f);
  metal(bp, t, end, 1.1f);
}
static void d_shaker(DARGS) { NOISE(out, t, .f = 6500, .q = 1.4f, .a = .012f, .tau = .025f, .peak = v * .55f); }
static void d_tamb(DARGS) {
  noise(out, t, (NO){.type = F_HP, .f = 6500, .q = .7f, .a = .002f, .tau = .05f, .peak = v * .45f});
  NOISE(out, t + .013, .f = 9000, .q = 2, .a = .001f, .tau = .06f, .peak = v * .25f);
}
static void d_conga(DARGS) { hand(out, t, v, 340, .11f); }
static void d_tumba(DARGS) { hand(out, t, v, 235, .15f); }
static void d_bongo(DARGS) { hand(out, t, v, 520, .055f); }
static void d_bongolo(DARGS) { hand(out, t, v, 395, .07f); }
static void d_clave(DARGS) { PART(out, t, 2450, .a = .001f, .tau = .022f, .peak = v * .6f); NOISE(out, t, .f = 2450, .q = 8, .tau = .01f, .peak = v * .2f); }
static void d_block(DARGS) { PART(out, t, 880, .a = .001f, .tau = .028f, .peak = v * .6f); PART(out, t, 1460, .a = .001f, .tau = .014f, .peak = v * .25f); NOISE(out, t, .f = 900, .q = 6, .tau = .015f, .peak = v * .25f); }
static void d_cowbell(DARGS) {
  int g = G(0), bp = F(F_BP, 820, 1.6f, 0); C(bp, g); C(g, out);
  double end = perc(PRM(g, 0), t, .001f, .085f, v * .7f, 0, .06f);
  C(O(W_SQUARE, 545, t, end, NULL, 1, 0), bp); C(O(W_SQUARE, 815, t, end, NULL, 1, 0), bp);
}
static void d_guiro(DARGS) { for (int i = 0; i < 10; i++) NOISE(out, t + i * .016, .f = 2900, .q = 2, .tau = .004f, .peak = v * .32f * (.55f + .45f * i / 9)); }
static void d_tomlo(DARGS) { tom(out, t, v, 92); }
static void d_tommid(DARGS) { tom(out, t, v, 132); }
static void d_tomhi(DARGS) { tom(out, t, v, 182); }
static void d_bodhran(DARGS) { PART(out, t, 78, .a = .003f, .tau = .13f, .peak = v * .9f, .bend = 1.5f, .bendTau = .02f); PART(out, t, 128, .a = .002f, .tau = .05f, .peak = v * .25f); NOISE(out, t, .f = 420, .q = 1, .tau = .025f, .peak = v * .4f); }
static void d_timbale(DARGS) { PART(out, t, 430, .a = .001f, .tau = .2f, .peak = v * .5f, .bend = 1.08f); PART(out, t, 655, .a = .001f, .tau = .12f, .peak = v * .25f); noise(out, t, (NO){.type = F_HP, .f = 2000, .q = .5f, .tau = .03f, .peak = v * .35f}); }
static void d_tri(DARGS) { PART(out, t, 2650, .a = .001f, .tau = .7f, .peak = v * .22f); PART(out, t, 4140, .a = .001f, .tau = .4f, .peak = v * .1f); PART(out, t, 6320, .a = .001f, .tau = .22f, .peak = v * .07f); }
static void d_clap(DARGS) { float o[3] = {0, .011f, .022f}; for (int i = 0; i < 3; i++) NOISE(out, t + o[i], .f = 1300, .q = 1, .tau = .006f, .peak = v * .5f); NOISE(out, t + .03, .f = 1200, .q = .8f, .tau = .07f, .peak = v * .4f); }
static void d_gong(DARGS) {
  static const float R[7][3] = {{1, 1, 4}, {1.48f, .7f, 3.2f}, {1.97f, .6f, 2.6f}, {2.34f, .5f, 2.2f}, {2.9f, .35f, 1.6f}, {3.6f, .3f, 1.3f}, {4.4f, .2f, 1}};
  for (int i = 0; i < 7; i++) PART(out, t, 72 * R[i][0], .a = i ? .25f : .02f, .tau = R[i][2], .peak = v * R[i][1] * .4f);
  noise(out, t, (NO){.type = F_LP, .f = 2000, .q = .5f, .tau = .4f, .peak = v * .12f});
}
static void d_thunder(DARGS) {
  int n = noiseSrc(t, t + 9), lp = F(F_LP, 220, .5f, 0), g = G(0);
  Param *q = PRM(g, 0); pins(q, P_SET, t, 0, 0); pins(q, P_LIN, t + .35, v * 1.2f, 0); pins(q, P_TGT, t + .35, v * .5f, .4f); pins(q, P_TGT, t + 1.6, 0, 1.2f);
  Param *fq = PRM(lp, 0); pins(fq, P_SET, t, 600, 0); pins(fq, P_TGT, t + .2, 160, .8f);
  C(n, lp); C(lp, g); C(g, out);
  noise(out, t + .05, (NO){.type = F_LP, .f = 1400, .q = .5f, .a = .01f, .tau = .2f, .peak = v * .35f});
}
static void d_surf(DARGS) {
  int n = noiseSrc(t, t + 7), lp = F(F_LP, 300, .4f, 0), g = G(0);
  Param *fq = PRM(lp, 0); pins(fq, P_SET, t, 300, 0); pins(fq, P_LIN, t + 1.5, 1500, 0); pins(fq, P_LIN, t + 4.5, 450, 0);
  Param *q = PRM(g, 0); pins(q, P_SET, t, 0, 0); pins(q, P_LIN, t + 1.5, v * .55f, 0); pins(q, P_TGT, t + 1.6, 0, .9f);
  C(n, lp); C(lp, g); C(g, out);
}
typedef void (*HitFn)(DARGS);
static const struct { HitFn fn; float rev, level; } DRUM[] = { /* same order as DRUMS[] */
  {d_kick, .05f, .95f}, {d_snare, .25f, 1.12f}, {d_rim, .2f, 1.66f}, {d_hat, .1f, .79f}, {d_ohat, .15f, .56f}, {d_ride, .25f, 1.65f},
  {d_crash, .3f, .75f}, {d_shaker, .1f, 1.21f}, {d_tamb, .15f, .76f}, {d_conga, .18f, .84f}, {d_tumba, .18f, .76f}, {d_bongo, .15f, .91f},
  {d_bongolo, .15f, .82f}, {d_clave, .25f, .83f}, {d_block, .25f, .98f}, {d_cowbell, .2f, .54f}, {d_guiro, .15f, 3.85f},
  {d_tomlo, .25f, .74f}, {d_tommid, .25f, .79f}, {d_tomhi, .25f, .83f}, {d_bodhran, .2f, .76f}, {d_timbale, .25f, .74f},
  {d_tri, .4f, .44f}, {d_clap, .3f, 3.57f}, {d_gong, .6f, .46f}, {d_thunder, .5f, 2.38f}, {d_surf, .5f, 1.42f}};

/* --- note lifecycle --- */
static int nactive;
static void dfs(Note *nt, int k, char *seen) {
  if (seen[k]) return; seen[k] = 1;
  Node *n = &nt->n[k];
  for (int i = 0; i < n->nin; i++) dfs(nt, n->in[i], seen);
  for (int w = 0; w < 2; w++) for (int i = 0; i < n->p[w].nmod; i++) dfs(nt, n->p[w].mod[i], seen);
  nt->order[nt->no++] = k;
}
static Note *note_begin(int ch, double t) {
  Note *best = NULL;
  for (int i = 0; i < MAXNOTES; i++) if (!notes[i].used) { best = &notes[i]; break; }
  if (!best) { best = &notes[0]; for (int i = 1; i < MAXNOTES; i++) if (notes[i].end < best->end) best = &notes[i]; nactive--; } /* steal */
  best->used = 1; best->ch = ch; best->end = t + .05; best->nn = 0; best->no = 0;
  NB = best; G(1); /* node 0 = note output */
  return best;
}
static void note_finish(Note *nt) {
  char seen[MAXNODE] = {0}; dfs(nt, 0, seen); nt->end += .05; nactive++;
}

static void biq(Node *n, float f) {
  double w0 = 2 * M_PI * f / SR, c = cos(w0), s = sin(w0), b0, b1, b2, a0, a1, a2;
  switch (n->ftype) {
  case F_LP: { double al = s / (2 * pow(10, n->q / 20)); b0 = (1 - c) / 2; b1 = 1 - c; b2 = b0; a0 = 1 + al; a1 = -2 * c; a2 = 1 - al; break; }
  case F_HP: { double al = s / (2 * pow(10, n->q / 20)); b0 = (1 + c) / 2; b1 = -(1 + c); b2 = b0; a0 = 1 + al; a1 = -2 * c; a2 = 1 - al; break; }
  case F_BP: { double al = s / (2 * n->q); b0 = al; b1 = 0; b2 = -al; a0 = 1 + al; a1 = -2 * c; a2 = 1 - al; break; }
  case F_PEAK: { double A = pow(10, n->gdb / 40), al = s / (2 * n->q); b0 = 1 + al * A; b1 = -2 * c; b2 = 1 - al * A; a0 = 1 + al / A; a1 = -2 * c; a2 = 1 - al / A; break; }
  case F_LS: { double A = pow(10, n->gdb / 40), al = s / 2 * sqrt(2), sa = 2 * sqrt(A) * al;
    b0 = A * ((A + 1) - (A - 1) * c + sa); b1 = 2 * A * ((A - 1) - (A + 1) * c); b2 = A * ((A + 1) - (A - 1) * c - sa);
    a0 = (A + 1) + (A - 1) * c + sa; a1 = -2 * ((A - 1) + (A + 1) * c); a2 = (A + 1) + (A - 1) * c - sa; break; }
  default: { double A = pow(10, n->gdb / 40), al = s / 2 * sqrt(2), sa = 2 * sqrt(A) * al;
    b0 = A * ((A + 1) + (A - 1) * c + sa); b1 = -2 * A * ((A - 1) + (A + 1) * c); b2 = A * ((A + 1) + (A - 1) * c - sa);
    a0 = (A + 1) - (A - 1) * c + sa; a1 = 2 * ((A - 1) - (A + 1) * c); a2 = (A + 1) - (A - 1) * c - sa; }
  }
  n->b0 = b0 / a0; n->b1 = b1 / a0; n->b2 = b2 / a0; n->a1 = a1 / a0; n->a2 = a2 / a0; n->lastf = f;
}
static inline float biq_run(Node *n, float x) { float y = n->b0 * x + n->z1; n->z1 = n->b1 * x - n->a1 * y + n->z2; n->z2 = n->b2 * x - n->a2 * y; return y; }
static inline float polyblep(double t, double dt) {
  if (t < dt) { t /= dt; return t + t - t * t - 1; }
  if (t > 1 - dt) { t = (t - 1) / dt; return t * t + t + t + 1; }
  return 0;
}
static inline float pval(Note *nt, Param *p, double t, int i) {
  float v = pnext(p, t);
  for (int k = 0; k < p->nmod; k++) v += nt->n[p->mod[k]].out[i];
  return v;
}
static void note_render(Note *nt, int64_t s0, float *chbuf) {
  for (int oi = 0; oi < nt->no; oi++) {
    Node *n = &nt->n[nt->order[oi]];
    float in[BLK];
    if (n->type == N_GAIN || n->type == N_FILT) {
      memset(in, 0, sizeof in);
      for (int k = 0; k < n->nin; k++) { float *o = nt->n[n->in[k]].out; for (int i = 0; i < BLK; i++) in[i] += o[i]; }
    }
    for (int i = 0; i < BLK; i++) {
      double t = (double)(s0 + i) / SR;
      switch (n->type) {
      case N_GAIN: n->out[i] = in[i] * pval(nt, &n->p[0], t, i); break;
      case N_FILT: { float f = clampf(pval(nt, &n->p[0], t, i), 10, NYQ * .95f);
        if (f != n->lastf && (n->lastf < 0 || fabsf(f - n->lastf) > n->lastf * 0.002f || (i & 15) == 0)) biq(n, f);
        n->out[i] = biq_run(n, in[i]); break; }
      case N_OSC: {
        float f = pnext(&n->p[0], t), det = pval(nt, &n->p[1], t, i);
        if (t < n->start || t >= n->stop) { n->out[i] = 0; break; }
        if (det != 0) f *= exp2f(det / 1200.f);
        double dt = clampf(f, 0, NYQ) / SR, ph = n->phase, y;
        switch (n->wave) {
        case W_SINE: { double x = ph * 4096; int k = (int)x; float fr = x - k; y = sintab[k] + (sintab[k + 1] - sintab[k]) * fr; break; }
        case W_SAW: y = 2 * ph - 1 - polyblep(ph, dt); break;
        case W_SQUARE: y = (ph < .5 ? 1 : -1) + polyblep(ph, dt) - polyblep(fmod(ph + .5, 1), dt); break;
        case W_TRI: y = ph < .25 ? 4 * ph : ph < .75 ? 2 - 4 * ph : 4 * ph - 4; break;
        default: { double x = ph * 2048; int k = (int)x; float fr = x - k; const float *w = wt[n->wave]; y = w[k] + (w[(k + 1) & 2047] - w[k]) * fr; }
        }
        n->out[i] = y; ph += dt; if (ph >= 1) ph -= 1; n->phase = ph; break; }
      case N_NOISE:
        if (t < n->start || t >= n->stop) { n->out[i] = 0; break; }
        n->rng ^= n->rng << 13; n->rng ^= n->rng >> 17; n->rng ^= n->rng << 5;
        n->out[i] = (n->rng / 2147483648.0f) - 1; break;
      case N_BUF:
        if (t < n->start || t >= n->stop) { n->out[i] = 0; break; }
        { int k = (int)n->pos; if (k + 1 >= n->blen) { n->out[i] = 0; break; }
          float fr = n->pos - k; n->out[i] = n->buf[k] + (n->buf[k + 1] - n->buf[k]) * fr; n->pos += n->rate; }
        break;
      }
    }
  }
  float *o = nt->n[0].out; for (int i = 0; i < BLK; i++) chbuf[i] += o[i];
}

/* --- master section --- */
typedef struct { float thr, knee, ratio, att, rel, makeup, env; } Comp;
static float comp_curve(Comp *c, float x) {
  if (x <= c->thr) return x;
  if (c->knee > 0 && x < c->thr + c->knee) { float d = x - c->thr; return x + (1 / c->ratio - 1) * d * d / (2 * c->knee); }
  float kneeOut = c->thr + c->knee - (1 - 1 / c->ratio) * c->knee / 2;
  return kneeOut + (x - c->thr - c->knee) / c->ratio;
}
static void comp_init(Comp *c, float thr, float knee, float ratio, float att, float rel) {
  c->thr = thr; c->knee = knee; c->ratio = ratio; c->att = expf(-1 / (att * SR)); c->rel = expf(-1 / (rel * SR)); c->env = 0;
  c->makeup = powf(10, -comp_curve(c, 0) * .6f / 20); /* Chromium-style auto makeup (1/fullRangeGain)^0.6 */
}
static inline float comp_gain(Comp *c, float lvl) {
  float x = 20 * log10f(lvl + 1e-9f), red = x - comp_curve(c, x);
  float co = red > c->env ? c->att : c->rel; c->env = red + (c->env - red) * co;
  return powf(10, -c->env / 20) * c->makeup;
}

/* Freeverb (stands in for the 2.8 s convolution IR) */
#define NCOMB 8
#define NAP 4
static const int combT[NCOMB] = {1116, 1188, 1277, 1356, 1422, 1491, 1557, 1617}, apT[NAP] = {556, 441, 341, 225};
typedef struct { float *b; int n, i; float s; } Line;
static struct { Line c[2][NCOMB], a[2][NAP]; float fb, damp, gain; } rv;
static void line_init(Line *l, int n) { l->n = n; l->b = calloc(n, sizeof(float)); l->i = 0; l->s = 0; }
static void reverb_init(void) {
  for (int ch = 0; ch < 2; ch++) {
    for (int k = 0; k < NCOMB; k++) line_init(&rv.c[ch][k], (combT[k] + ch * 23) * SR / 44100);
    for (int k = 0; k < NAP; k++) line_init(&rv.a[ch][k], (apT[k] + ch * 23) * SR / 44100);
  }
  rv.fb = .918f; rv.damp = .35f; rv.gain = .015f;
}
static void reverb(float x, float *L, float *R) {
  float in = x * rv.gain, o[2];
  for (int ch = 0; ch < 2; ch++) {
    float s = 0;
    for (int k = 0; k < NCOMB; k++) { Line *l = &rv.c[ch][k]; float y = l->b[l->i]; l->s = y * (1 - rv.damp) + l->s * rv.damp; l->b[l->i] = in + l->s * rv.fb; if (++l->i >= l->n) l->i = 0; s += y; }
    for (int k = 0; k < NAP; k++) { Line *l = &rv.a[ch][k]; float b = l->b[l->i]; l->b[l->i] = s + b * .5f; s = b - s; if (++l->i >= l->n) l->i = 0; }
    o[ch] = s;
  }
  *L = o[0]; *R = o[1];
}
static float verbCal = 1;

typedef struct { float vol, rev, gl, gr; float buf[BLK]; } Chan;
static Chan chans[MAXV];
static Node shelfL[2], shelfH[2], verbHP; static Comp comp, lim;
static float verbRet, masterVol = 1;

static void engine_init(void) {
  init_tables(); reverb_init();
  notes = calloc(MAXNOTES, sizeof(Note));
  verbRet = .25f + 1.6f * song.reverb;
  for (int i = 0; i < song.nv; i++) {
    Voice *v = &song.v[i];
    float level = v->drum ? DRUM[v->inst].level : INST[v->inst].level, drev = v->drum ? DRUM[v->inst].rev : INST[v->inst].rev;
    chans[i].vol = v->vol * level; chans[i].rev = v->rev >= 0 ? v->rev : drev;
    float x = (v->pan + 1) / 2; chans[i].gl = cosf(x * M_PI / 2); chans[i].gr = sinf(x * M_PI / 2);
  }
  for (int c = 0; c < 2; c++) { shelfL[c].ftype = F_LS; shelfL[c].gdb = 2; biq(&shelfL[c], 180); shelfH[c].ftype = F_HS; shelfH[c].gdb = -2.5f; biq(&shelfH[c], 7500); }
  verbHP.ftype = F_HP; verbHP.q = .6f; biq(&verbHP, 220);
  comp_init(&comp, -15, 10, 3.2f, .006f, .22f);
  comp_init(&lim, -3, 0, 20, .001f, .1f);
  /* calibrate Freeverb so white noise in gives ~ the normalised convolver's output level (~0.42x RMS) */
  { double si = 0, so = 0; uint32_t r = 12345;
    for (int i = 0; i < SR * 3; i++) { r ^= r << 13; r ^= r >> 17; r ^= r << 5; float x = r / 2147483648.0f - 1, L, R; reverb(x, &L, &R); if (i > SR) { si += x * x; so += L * L; } }
    verbCal = .42f / sqrt(so / si);
    for (int ch = 0; ch < 2; ch++) { for (int k = 0; k < NCOMB; k++) { memset(rv.c[ch][k].b, 0, rv.c[ch][k].n * 4); rv.c[ch][k].s = 0; } for (int k = 0; k < NAP; k++) memset(rv.a[ch][k].b, 0, rv.a[ch][k].n * 4); } }
}

static void trigger(TEv *ev, double t) {
  Voice *v = &song.v[ev->v];
  if (v->drum) { Note *nt = note_begin(ev->v, t); DRUM[v->inst].fn(0, t, ev->vel); note_finish(nt); return; }
  int n = ev->nm; float vs = ev->vel / sqrtf(n);
  for (int i = 0; i < n; i++) {
    P p = {0, v->glide, v->bright, v->att, v->rel};
    p.from = (ev->has_g && i == n - 1) ? mtof(ev->g) : 0;
    Note *nt = note_begin(ev->v, t);
    INST[v->inst].fn(0, t, ev->d, mtof(ev->m[i]), vs, &p);
    note_finish(nt);
  }
}

/* render one block into interleaved stereo float */
static void render_block(int64_t s0, float *out) {
  for (int c = 0; c < song.nv; c++) memset(chans[c].buf, 0, sizeof chans[c].buf);
  double tEnd = (double)(s0 + BLK) / SR;
  for (int i = 0; i < MAXNOTES; i++) {
    Note *nt = &notes[i]; if (!nt->used) continue;
    if (nt->end < (double)s0 / SR) { nt->used = 0; nactive--; continue; }
    note_render(nt, s0, chans[nt->ch].buf);
  }
  (void)tEnd;
  for (int i = 0; i < BLK; i++) {
    float L = 0, R = 0, send = 0;
    for (int c = 0; c < song.nv; c++) { float x = chans[c].buf[i] * chans[c].vol; L += x * chans[c].gl; R += x * chans[c].gr; send += x * chans[c].rev; }
    float rl, rr; reverb(biq_run(&verbHP, send), &rl, &rr);
    L += rl * verbCal * verbRet; R += rr * verbCal * verbRet;
    L *= .72f; R *= .72f;
    L = biq_run(&shelfH[0], biq_run(&shelfL[0], L)); R = biq_run(&shelfH[1], biq_run(&shelfL[1], R));
    float g = comp_gain(&comp, fmaxf(fabsf(L), fabsf(R))); L *= g; R *= g;
    g = comp_gain(&lim, fmaxf(fabsf(L), fabsf(R))); L *= g; R *= g;
    out[2 * i] = L * masterVol; out[2 * i + 1] = R * masterVol;
  }
}

/* ======================================================================
 *  SCHEDULER, SCROLLING VIEW, OUTPUT
 * ====================================================================== */
static volatile sig_atomic_t stop_flag;
static void on_sig(int s) { (void)s; stop_flag = 1; }

typedef struct { Timeline *T; int idx; double off; int pass; } Cursor;
static int maxLoops = -1; static double maxSecs = 0;
#define T0 0.10
/* yields next event in playback order; returns 0 when finished */
static int next_ev(Cursor *c, TEv **e, double *t) {
  for (;;) {
    if (c->idx < c->T->n) { *e = &c->T->e[c->idx++]; *t = (*e)->t + c->off + T0; return 1; }
    if (c->T == &intro) { c->T = &loopT; c->idx = 0; c->off = intro.dur; c->pass = 0; if (!loopT.n || (maxLoops == 0)) return 0; continue; }
    c->pass++;
    if (!loopT.dur || (maxLoops >= 0 && c->pass >= maxLoops)) return 0;
    c->idx = 0; c->off += loopT.dur;
  }
}

/* ---- scrolling view ---- */
static FILE *vo; static int useColor = 1, colw[MAXV], vis[MAXV], nvis;
typedef struct { Timeline *T; int si; int step; double off; int pass; } RowCur;
static const int PAL[] = {203, 215, 227, 120, 87, 75, 141, 213, 210, 156, 117, 183, 222, 85, 111, 177};
static int termw(void) { struct winsize w; if (vo && ioctl(fileno(vo), TIOCGWINSZ, &w) == 0 && w.ws_col > 20) return w.ws_col; return 100; }
static void view_init(void) {
  int width = termw() - 9, used = 0;
  for (int vi = 0; vi < song.nv; vi++) {
    int w = song.v[vi].drum ? 2 : 4;
    for (int pi = 0; pi < song.npat; pi++) if (cp[pi].compiled && cp[pi].has[vi]) for (int k = 0; k < cp[pi].pv[vi].n; k++) { int l = strlen(cp[pi].pv[vi].e[k].label) + 1; if (l > w) w = l; }
    if (w > 8) w = 8;
    int hw = strlen(song.v[vi].name) + 1; if (song.v[vi].drum && hw > w) w = hw > 5 ? 5 : hw; else if (hw > w && w < 6) w = hw > 6 ? 6 : hw;
    if (used + w > width) break;
    colw[vi] = w; vis[nvis++] = vi; used += w;
  }
}
static void col_on(int vi) { if (useColor) fprintf(vo, "\033[38;5;%dm", PAL[vi % 16]); }
static void col_off(void) { if (useColor) fputs("\033[0m", vo); }
static void view_header(void) {
  if (!vo) return;
  fprintf(vo, "\r\n%s%s%s", useColor ? "\033[1m" : "", song.title, useColor ? "\033[0m" : "");
  if (song.composer[0]) fprintf(vo, "  by %s", song.composer);
  fprintf(vo, "  (%g bpm)\r\n", song.tempo);
  if (song.about[0]) fprintf(vo, "%s\r\n", song.about);
  fprintf(vo, "        ");
  for (int k = 0; k < nvis; k++) { int vi = vis[k]; col_on(vi); fprintf(vo, "%-*.*s", colw[vi], colw[vi] - 1, song.v[vi].name); col_off(); }
  if (nvis < song.nv) fprintf(vo, "+%d", song.nv - nvis);
  fputs("\r\n", vo); fflush(vo);
}
static double row_time(RowCur *r) { Sect *s = &r->T->s[r->si]; int st = r->step; return r->off + s->start + (st + ((st % 2 == 1) ? s->sw : 0)) * s->stepDur + T0; }
static int row_valid(RowCur *r) {
  for (;;) {
    if (r->si < r->T->ns) { if (r->step < r->T->s[r->si].total) return 1; r->si++; r->step = 0; continue; }
    if (r->T == &intro) { r->T = &loopT; r->si = 0; r->step = 0; r->off = intro.dur; r->pass = 0; if (!loopT.ns || maxLoops == 0) return 0; continue; }
    r->pass++;
    if (!loopT.ns || (maxLoops >= 0 && r->pass >= maxLoops)) return 0;
    r->si = 0; r->step = 0; r->off += loopT.dur;
  }
}
static void print_row(RowCur *r) {
  Sect *s = &r->T->s[r->si]; CPat *p = &cp[s->pat]; int st = r->step, bs = p->barSteps;
  if (st == 0) {
    if (useColor) fputs("\033[2m", vo);
    char lab[80]; snprintf(lab, sizeof lab, "%s%s%+d", p->name, "", s->trans);
    if (!s->trans) snprintf(lab, sizeof lab, "%s", p->name);
    fprintf(vo, "------- %s", lab);
    if (s->times > 1) fprintf(vo, " (%d/%d)", s->rep + 1, s->times);
    if (r->T == &loopT) fprintf(vo, "  [loop %d]", r->pass + 1);
    fputs(" -------", vo); col_off(); fputs("\r\n", vo);
  }
  if (st % bs == 0) fprintf(vo, "%s%4d   %s ", useColor ? "\033[1m" : "", st / bs + 1, useColor ? "\033[0m" : "");
  else if (st % p->steps == 0) fprintf(vo, "%4s.%-2d ", "", (st % bs) / p->steps + 1);
  else fputs("        ", vo);
  for (int k = 0; k < nvis; k++) {
    int vi = vis[k], w = colw[vi]; const char *cell = NULL; int cont = 0;
    if (p->has[vi]) for (int j = 0; j < p->pv[vi].n; j++) { PEv *e = &p->pv[vi].e[j]; if (e->step == st) { cell = e->label; break; } if (!song.v[vi].drum && e->step < st && e->step + e->len > st) cont = 1; }
    if (cell) { col_on(vi); if (useColor && (cell[0]=='X' || cell[0]=='[')) fputs("\033[1m", vo); fprintf(vo, "%-*.*s", w, w - 1, cell); col_off(); }
    else if (cont) { col_on(vi); if (useColor) fputs("\033[2m", vo); fprintf(vo, "%-*s", w, "|"); col_off(); }
    else { if (useColor) fputs("\033[2m", vo); fprintf(vo, "%-*s", w, "."); col_off(); }
  }
  fputs("\r\n", vo);
}

/* ---- audio sinks ---- */
static FILE *wavf; static int rawOut; static int64_t wavFrames;
static void wav_hdr(FILE *f, uint32_t frames) {
  uint32_t data = frames * 4, riff = 36 + data, sr = SR, br = SR * 4, fmtlen = 16; uint16_t fmt = 1, ch = 2, ba = 4, bits = 16;
  fwrite("RIFF", 1, 4, f); fwrite(&riff, 4, 1, f); fwrite("WAVEfmt ", 1, 8, f); fwrite(&fmtlen, 4, 1, f);
  fwrite(&fmt, 2, 1, f); fwrite(&ch, 2, 1, f); fwrite(&sr, 4, 1, f); fwrite(&br, 4, 1, f); fwrite(&ba, 2, 1, f); fwrite(&bits, 2, 1, f);
  fwrite("data", 1, 4, f); fwrite(&data, 4, 1, f);
}
#if !defined(NO_AUDIO) && !defined(USE_SDL)
static snd_pcm_t *pcm;
static int audio_open(void) {
  int e = snd_pcm_open(&pcm, getenv("SCRIM_ALSA") ? getenv("SCRIM_ALSA") : "default", SND_PCM_STREAM_PLAYBACK, 0);
  if (e < 0) { fprintf(stderr, "ALSA: %s\n", snd_strerror(e)); return -1; }
  if ((e = snd_pcm_set_params(pcm, SND_PCM_FORMAT_S16_LE, SND_PCM_ACCESS_RW_INTERLEAVED, 2, SR, 1, 120000)) < 0) { fprintf(stderr, "ALSA: %s\n", snd_strerror(e)); return -1; }
  return 0;
}
static void audio_write(int16_t *s, int frames) {
  while (frames > 0 && !stop_flag) {
    snd_pcm_sframes_t w = snd_pcm_writei(pcm, s, frames);
    if (w < 0) { if (snd_pcm_recover(pcm, w, 1) < 0) { stop_flag = 1; return; } continue; }
    s += w * 2; frames -= w;
  }
}
static int64_t audio_delay(void) { snd_pcm_sframes_t d = 0; if (snd_pcm_delay(pcm, &d) < 0) d = 0; return d; }
static void audio_close(int drain) { if (drain) snd_pcm_drain(pcm); else snd_pcm_drop(pcm); snd_pcm_close(pcm); }
#elif defined(USE_SDL)
static SDL_AudioDeviceID dev;
static int audio_open(void) {
  if (SDL_Init(SDL_INIT_AUDIO) < 0) { fprintf(stderr, "SDL: %s\n", SDL_GetError()); return -1; }
  SDL_AudioSpec want = {0}, have; want.freq = SR; want.format = AUDIO_S16SYS; want.channels = 2; want.samples = 1024;
  dev = SDL_OpenAudioDevice(NULL, 0, &want, &have, 0);
  if (!dev) { fprintf(stderr, "SDL: %s\n", SDL_GetError()); return -1; }
  SDL_PauseAudioDevice(dev, 0); return 0;
}
static void audio_write(int16_t *s, int frames) {
  SDL_QueueAudio(dev, s, frames * 4);
  while (!stop_flag && SDL_GetQueuedAudioSize(dev) > SR * 4 / 8) SDL_Delay(5); /* keep ~125 ms queued */
}
static int64_t audio_delay(void) { return SDL_GetQueuedAudioSize(dev) / 4; }
static void audio_close(int drain) { while (drain && !stop_flag && SDL_GetQueuedAudioSize(dev) > 0) SDL_Delay(10); SDL_CloseAudioDevice(dev); SDL_Quit(); }
#else
static int audio_open(void) { fprintf(stderr, "built without audio backend; use -w FILE or -r\n"); return -1; }
static void audio_write(int16_t *s, int f) { (void)s; (void)f; }
static int64_t audio_delay(void) { return 0; }
static void audio_close(int d) { (void)d; }
#endif

static char *read_all(FILE *f) {
  size_t cap = 1 << 16, n = 0; char *b = malloc(cap);
  for (size_t r; (r = fread(b + n, 1, cap - n - 1, f)) > 0;) { n += r; if (n + 1 >= cap) { cap *= 2; b = realloc(b, cap); } }
  b[n] = 0;
  for (size_t i = 0; i < n; i++) if (b[i] == '\r') b[i] = ' ';
  return b;
}
static void usage(void) {
  fputs("usage: scrimplay [-w out.wav | -r] [-l loops] [-t secs] [-v vol] [-c] [-q] [-n] [song.txt | -]\n"
        "  reads the score from a file or stdin; plays via "
#if defined(USE_SDL)
        "SDL2"
#elif defined(NO_AUDIO)
        "(no backend)"
#else
        "ALSA (env SCRIM_ALSA=device)"
#endif
        "\n  -w FILE wav out  -r raw s16le/48k/stereo to stdout  -l N loop passes  -t S seconds\n"
        "  -v master volume  -c check only  -q no scrolling view  -n no colour\n", stderr);
  exit(2);
}

int main(int argc, char **argv) {
  const char *wavPath = NULL; int check = 0, quiet = 0; int opt;
  while ((opt = getopt(argc, argv, "w:rl:t:v:cqnh")) != -1) switch (opt) {
    case 'w': wavPath = optarg; break; case 'r': rawOut = 1; break;
    case 'l': maxLoops = atoi(optarg); break; case 't': maxSecs = atof(optarg); break;
    case 'v': masterVol = atof(optarg); break; case 'c': check = 1; break;
    case 'q': quiet = 1; break; case 'n': useColor = 0; break; default: usage();
  }
  FILE *in = stdin;
  if (optind < argc && strcmp(argv[optind], "-")) { in = fopen(argv[optind], "r"); if (!in) { perror(argv[optind]); return 2; } }
  else if (optind >= argc && isatty(0)) usage();
  char *text = read_all(in);
  srand(0x5c121);
  compile_song(text);
  for (int i = 0; i < nerr; i++) fprintf(stderr, "line %d: %s\n", errs[i].line, errs[i].msg);
  if (check) { if (!nerr) fprintf(stderr, "ok: %d voices, %d patterns, intro %.1fs, loop %.1fs\n", song.nv, song.npat, intro.dur, loopT.dur); return nerr ? 1 : 0; }
  if (!intro.dur && !loopT.dur) return 1;
  if ((wavPath || rawOut) && maxLoops < 0 && !maxSecs) maxLoops = 1;
  if (rawOut && isatty(1)) { fputs("refusing to write raw audio to a terminal\n", stderr); return 2; }

  /* where the scrolling view goes: stdout if it's a terminal, else stderr when audio owns stdout */
  if (!quiet) { if (!rawOut && isatty(1)) vo = stdout; else if (isatty(2)) vo = stderr; }
  if (!vo || getenv("NO_COLOR")) useColor = vo ? useColor && !getenv("NO_COLOR") : 0;
  signal(SIGINT, on_sig); signal(SIGTERM, on_sig); signal(SIGPIPE, on_sig);
  engine_init();
  int live = !wavPath && !rawOut;
  if (live && audio_open() < 0) return 1;
  if (wavPath) { wavf = fopen(wavPath, "wb"); if (!wavf) { perror(wavPath); return 1; } wav_hdr(wavf, 0); }
  if (vo) { view_init(); view_header(); }

  Cursor cur = {&intro, 0, 0, 0}; TEv *pe = NULL; double pt = 0; int have = next_ev(&cur, &pe, &pt);
  RowCur rc = {&intro, 0, 0, 0, 0}; int rowsLeft = vo ? row_valid(&rc) : 0;
  int64_t s0 = 0; double tailUntil = -1;
  enum { CH = 1024 }; float fbuf[BLK * 2]; int16_t obuf[CH * 2]; int on = 0;
  while (!stop_flag) {
    double tb = (double)(s0 + BLK) / SR;
    while (have && pt < tb) {
      if (maxSecs && pt > maxSecs) { have = 0; break; }
      trigger(pe, pt); have = next_ev(&cur, &pe, &pt);
    }
    if (!have && tailUntil < 0) tailUntil = (maxSecs && maxSecs < tb ? tb : tb) + 2.5; /* let tails + reverb ring */
    if (tailUntil > 0 && tb > tailUntil) break;
    render_block(s0, fbuf);
    for (int i = 0; i < BLK * 2; i++) { float x = fbuf[i]; x = x > 1 ? 1 : x < -1 ? -1 : x; obuf[on * 2 + i] = (int16_t)lrintf(x * 32767); }
    on += BLK; s0 += BLK;
    if (on == CH) {
      if (live) audio_write(obuf, CH);
      else if (wavf) { fwrite(obuf, 4, CH, wavf); wavFrames += CH; }
      else if (fwrite(obuf, 4, CH, stdout) != CH) break;
      on = 0;
      if (vo && rowsLeft) {
        double played = (double)(s0 - (live ? audio_delay() : 0)) / SR;
        while (rowsLeft && row_time(&rc) <= played) {
          if (!have && tailUntil > 0 && row_time(&rc) > tb) { rowsLeft = 0; break; }
          print_row(&rc); rc.step++; rowsLeft = row_valid(&rc);
        }
        fflush(vo);
      }
    }
  }
  if (on) { if (live) audio_write(obuf, on); else if (wavf) { fwrite(obuf, 4, on, wavf); wavFrames += on; } else fwrite(obuf, 4, on, stdout); }
  if (vo) { col_off(); fputs(stop_flag ? "\r\n[stopped]\r\n" : "\r\n", vo); fflush(vo); }
  if (live) audio_close(!stop_flag);
  if (wavf) { fseek(wavf, 0, SEEK_SET); wav_hdr(wavf, (uint32_t)wavFrames); fclose(wavf); fprintf(stderr, "wrote %s (%.1fs)\n", wavPath, (double)wavFrames / SR); }
  return 0;
}
