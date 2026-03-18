/*
 * watch - execute a program repeatedly, displaying output fullscreen
 *
 * Copyright © 2023 Roman Žilka <roman.zilka@gmail.com>
 * Copyright © 2010-2023 Jim Warner <james.warner@comcast.net>
 * Copyright © 2015-2026 Craig Small <csmall@dropbear.xyz>
 * Copyright © 2011-2012 Sami Kerola <kerolasa@iki.fi>
 * Copyright © 2002-2007 Albert Cahalan
 * Copyright © 1999      Mike Coleman <mkc@acm.org>.
 *
 * Based on the original 1991 'watch' by Tony Rems <rembo@unisoft.com>
 * (with mods and corrections by Francois Pinard).
 *
 * stderr handling, exec, and beep option added by Morty Abzug, 2008
 * Unicode Support added by Jarrod Lowe <procps@rrod.net> in 2009.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

#ifdef WITH_WATCH8BIT
# define _XOPEN_SOURCE_EXTENDED 1
# include <wctype.h>
#else
# include <ctype.h>
#endif
#ifdef HAVE_NCURSESW_NCURSES_H
# include <ncursesw/ncurses.h>
#else
# include <ncurses.h>
#endif
#include <assert.h>
#include <fcntl.h>
#include <getopt.h>
#include <inttypes.h>
#include <limits.h>
#include <locale.h>
#include <wchar.h>
#include <signal.h>
#include <math.h>
#include <strings.h>
#include <pwd.h>
#include <sys/ioctl.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <pty.h>
#include "c.h"
#include "config.h"
#include "fileutils.h"
#include "nls.h"
#include "signals.h"
#include "strutils.h"
#include "xalloc.h"

#ifdef FORCE_8BIT
# undef isprint
# define isprint(x) ( (x>=' '&&x<='~') || (x>=0xa0) )
#endif

#ifdef WITH_WATCH8BIT
#define XL(c) L ## c
#define XEOF WEOF
#define Xint wint_t
#define Xgetc(stream) getmb(stream)
#else
#define XL(c) c
#define XEOF EOF
#define Xint int
#define Xgetc(stream) getc(stream)
#endif

#define HEIGHT_FALLBACK 24
#define WIDTH_FALLBACK 80
#define TAB_WIDTH 8
#define MAX_ANSIBUF 100
#define HEADER_HEIGHT 2

/* Boolean command line options */
#define WATCH_DIFF     (1 << 0)
#define WATCH_CUMUL    (1 << 1)
#define WATCH_EXEC     (1 << 2)
#define WATCH_BEEP     (1 << 3)
#define WATCH_COLOR    (1 << 4)
#define WATCH_ERREXIT  (1 << 5)
#define WATCH_CHGEXIT  (1 << 6)
#define WATCH_EQUEXIT  (1 << 7)
#define WATCH_NORERUN  (1 << 8)
#define WATCH_PRECISE  (1 << 9)
#define WATCH_NOWRAP   (1 << 10)
#define WATCH_NOTITLE  (1 << 11)
#define WATCH_FOLLOW   (1 << 12)
// Do we care about screen contents changes at all?
#define WATCH_ALL_DIFF (WATCH_DIFF | WATCH_CHGEXIT | WATCH_EQUEXIT)

static uf16 flags;
static int height, width;
static bool first_screen = true, screen_size_changed, screen_changed;
static double interval_real = 2;
static char *command;
static size_t command_len;
static char *const *command_argv;
static const char *shotsdir = "";
static bool use_pty;
static bool use_ansi;
static bool termios_active;
static struct termios termios_orig;
static bool color_option_seen;
static bool color_explicit;
static volatile sig_atomic_t ansi_exit_newline = 0;
static char **ansi_prev_lines;
static char **ansi_prev_plain;
static int *ansi_line_age;
static bool *ansi_line_seen;
static int ansi_prev_count;
static int16_t **ansi_char_age;
static size_t *ansi_char_age_len;
static char **ansi_pending_lines;
static char **ansi_pending_plain;
static int16_t **ansi_pending_ages;
static size_t *ansi_pending_age_len;
static bool ansi_pending_active;
static int ansi_pending_frames;
static int ansi_fade_cycles = 8;
static int ansi_fade_fps = 12;
static double ansi_fade_seconds = 1.0;
static bool ansi_fade_half_life = false;
static int ansi_fade_half_life_frames = 0;
static int ansi_fade_max_brightness = 255;
static int ansi_fade_bg_r = 255;
static int ansi_fade_bg_g = 200;
static int ansi_fade_bg_b = 0;
static double ansi_fade_in_seconds = 0.0;
static int ansi_fade_in_frames = 0;
static bool ansi_default_fg_valid = false;
static int ansi_default_fg_r = 0;
static int ansi_default_fg_g = 0;
static int ansi_default_fg_b = 0;
static bool ansi_default_bg_valid = false;
static int ansi_default_bg_r = 0;
static int ansi_default_bg_g = 0;
static int ansi_default_bg_b = 0;

static void restore_terminal(void);
static void ansi_show_cursor(void);
static size_t utf8_seq_len(unsigned char c);
static size_t utf8_count_glyphs(const char *s);
static bool parse_rgb_env(const char *value, int *r, int *g, int *b);
static void xterm256_to_rgb(int n, int *r, int *g, int *b);
static void ansi_update_fg_from_sgr(const char *seq, size_t len, bool *fg_set, int *fr, int *fg, int *fb);
static void load_watch_prefs(void);
static char *ansi_truncate_visible(const char *line, int cols);
static void load_default_fg_from_env(void);
static void query_default_fg(void);
static void query_default_bg(void);
static bool parse_rgb_response(const char *rgb, int *r, int *g, int *b);
static void log_watch_debug(const char *label, int r, int g, int b, bool ok);
static void log_watch_settings(void);
static int16_t *build_fadein_ages(const char *prev, const char *next, size_t prev_glyphs);

typedef uf64 watch_usec_t;
#define USECS_PER_SEC ((watch_usec_t)1000000)  // same type

#define MAIN_HEIGHT (height - (flags & WATCH_NOTITLE?0:HEADER_HEIGHT))

WINDOW *mainwin;

// don't use EXIT_FAILURE, it can be anything and manpage makes guarantees about
// exitcodes
static void __attribute__ ((__noreturn__)) usage(FILE * out)
{
	fputs(USAGE_HEADER, out);
	fprintf(out, _(" %s [options] command\n"), program_invocation_short_name);
	fputs(USAGE_OPTIONS, out);
	// TODO: other tools in src/ use one leading blank
	fputs(_("  -b, --beep             beep if command has a non-zero exit\n"), out);
	fputs(_("  -c, --color            interpret ANSI color and style sequences\n"), out);
	fputs(_("  -C, --no-color         do not interpret ANSI color and style sequences\n"), out);
	fputs(_("  -d, --differences[=<permanent>]\n"
	        "                         highlight changes between updates\n"), out);
	fputs(_("  -e, --errexit          exit if command has a non-zero exit\n"), out);
        fputs(_("  -f, --follow           Follow the output and don't clear screen\n"), out);
	fputs(_("  -g, --chgexit          exit when output from command changes\n"), out);
	fputs(_("  -q, --equexit <cycles>\n"
	        "                         exit when output from command does not change\n"), out);
	fputs(_("  -n, --interval <secs>  seconds to wait between updates\n"), out);
	fputs(_("  -p, --precise          -n includes command running time\n"), out);  // TODO: gettext
	fputs(_("  -r, --no-rerun         do not rerun program on window resize\n"), out);
	fputs(_("  -s, --shotsdir         directory to store screenshots\n"), out);  // TODO: gettext
	fputs(_("  -t, --no-title         turn off header\n"), out);
	fputs(_("  -w, --no-wrap          turn off line wrapping\n"), out);
	fputs(_("  -x, --exec             pass command to exec instead of \"sh -c\"\n"), out);
	fputs(USAGE_SEPARATOR, out);
	fputs(_("Configuration file: ~/.watchrc\n"), out);
	fputs(USAGE_HELP, out);
	fputs(_(" -v, --version  output version information and exit\n"), out);
	fprintf(out, USAGE_MAN_TAIL("watch(1)"));

	exit(out == stderr ? 1 : EXIT_SUCCESS);
}

#define endwin_xerr(...) do { endwin(); err(__VA_ARGS__); } while (0)
#define endwin_error(...) do { endwin(); error(__VA_ARGS__); } while (0)
#define endwin_exit(status) do { endwin(); exit(status); } while (0)

static void die(int notused __attribute__ ((__unused__)))
{
	if (use_ansi) {
		ansi_exit_newline = 1;
		(void)!write(STDOUT_FILENO, "\n", 1);
		ansi_show_cursor();
		restore_terminal();
		exit(EXIT_SUCCESS);
	}
	endwin_exit(EXIT_SUCCESS);
}

static void winch_handler(int notused __attribute__ ((__unused__)))
{
	screen_size_changed = true;
}



static int attributes;  // TODO: attr_t likely has more value digits than int
static int nr_of_colors, fg_col, bg_col;
static bool more_colors;

static void reset_ansi(void)
{
	attributes = A_NORMAL;
	fg_col = 0;
	bg_col = 0;
}

static bool term_supports_truecolor(void)
{
	const char *colorterm = getenv("COLORTERM");
	if (colorterm && (!strcasecmp(colorterm, "truecolor") || !strcasecmp(colorterm, "24bit")))
		return true;
	const char *term = getenv("TERM");
	if (!term)
		return false;
	if (strstr(term, "direct"))
		return true;
	if (strstr(term, "truecolor"))
		return true;
	return false;
}

static void restore_terminal(void)
{
	if (termios_active) {
		tcsetattr(STDIN_FILENO, TCSANOW, &termios_orig);
		termios_active = false;
	}
}

static void setup_terminal_raw(void)
{
	struct termios t;
	if (tcgetattr(STDIN_FILENO, &termios_orig) == 0) {
		termios_active = true;
		t = termios_orig;
		t.c_lflag &= (tcflag_t)~(ICANON | ECHO);
		t.c_cc[VMIN] = 1;
		t.c_cc[VTIME] = 0;
		tcsetattr(STDIN_FILENO, TCSANOW, &t);
		atexit(restore_terminal);
	}
}

static void ansi_hide_cursor(void)
{
	const char *s = "\x1b[?25l";
	(void)!write(STDOUT_FILENO, s, strlen(s));
}

static void ansi_show_cursor(void)
{
	const char *s = "\x1b[?25h";
	(void)!write(STDOUT_FILENO, s, strlen(s));
}

static void ansi_clear_screen(void)
{
	const char *s = "\x1b[H\x1b[2J";
	(void)!write(STDOUT_FILENO, s, strlen(s));
}

static void ansi_move(int row, int col)
{
	char buf[32];
	int len = snprintf(buf, sizeof(buf), "\x1b[%d;%dH", row + 1, col + 1);
	if (len > 0)
		(void)!write(STDOUT_FILENO, buf, (size_t)len);
}

static char *strip_ansi_sgr(const char *line)
{
	size_t len = strlen(line);
	char *out = xmalloc(len + 1);
	size_t j = 0;
	for (size_t i = 0; i < len; i++) {
		if (line[i] == '\x1b' && line[i + 1] == '[') {
			i += 2;
			while (i < len && line[i] != 'm')
				i++;
			continue;
		}
		out[j++] = line[i];
	}
	out[j] = '\0';
	return out;
}

static void ansi_get_winsize(void)
{
	struct winsize ws;
	if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_row > 0 && ws.ws_col > 0) {
		height = ws.ws_row;
		width = ws.ws_col;
	} else {
		height = HEIGHT_FALLBACK;
		width = WIDTH_FALLBACK;
	}
}

static void ansi_write_line(int row, const char *line)
{
	ansi_move(row, 0);
	if (line && *line) {
		char *trunc = NULL;
		if (width > 0)
			trunc = ansi_truncate_visible(line, width);
		if (trunc) {
			(void)!write(STDOUT_FILENO, trunc, strlen(trunc));
			free(trunc);
		} else {
			(void)!write(STDOUT_FILENO, line, strlen(line));
		}
	}
	(void)!write(STDOUT_FILENO, "\x1b[49m", 5); // ensure default background before clear
	(void)!write(STDOUT_FILENO, "\x1b[K", 3); // clear to end of line
}

static char *ansi_compose_line(const char *left, const char *right)
{
	if (width <= 0) {
		return xstrdup("");
	}
	size_t w = (size_t)width;
	char *buf = xmalloc(w + 1);
	memset(buf, ' ', w);
	buf[w] = '\0';
	if (left && *left) {
		size_t l = strlen(left);
		if (l > w)
			l = w;
		memcpy(buf, left, l);
	}
	if (right && *right) {
		size_t r = strlen(right);
		if (r <= w) {
			size_t start = w - r;
			memcpy(buf + start, right, r);
		}
	}
	return buf;
}

static void ansi_output_headers(watch_usec_t span, uint8_t exitcode)
{
	if (flags & WATCH_NOTITLE)
		return;

	char left[256];
	char right[256];
	char low[128];

	snprintf(left, sizeof(left), "Every %.1fs: %s", interval_real, command);
	{
		char hostbuf[256];
		if (gethostname(hostbuf, sizeof(hostbuf)) != 0)
			hostbuf[0] = '\0';
		hostbuf[sizeof(hostbuf) - 1] = '\0';
		time_t t = time(NULL);
		char ts[128];
		size_t n = strftime(ts, sizeof(ts), "%c", localtime(&t));
		if (n == 0)
			ts[0] = '\0';
		snprintf(right, sizeof(right), "%s%s%s", hostbuf, hostbuf[0] ? ": " : "", ts);
	}

	if (span > USECS_PER_SEC * 24 * 60 * 60)
		snprintf(low, sizeof(low), "in >1 day (%" PRIu8 ")", exitcode);
	else if (span < 1000)
		snprintf(low, sizeof(low), "in <%.3fs (%" PRIu8 ")", 0.001, exitcode);
	else
		snprintf(low, sizeof(low), "in %.3Lfs (%" PRIu8 ")", (long double)span / USECS_PER_SEC, exitcode);

	char *line0 = ansi_compose_line(left, right);
	char *line1 = ansi_compose_line("", low);
	ansi_write_line(0, line0);
	ansi_write_line(1, line1);
	free(line0);
	free(line1);
}

static char *ansi_apply_background(const char *line, const char *bg)
{
	if (!bg || !*bg)
		return xstrdup(line ? line : "");
	size_t len = line ? strlen(line) : 0;
	size_t bglen = strlen(bg);
	size_t cap = len * 4 + bglen * 8 + 32;
	char *out = xmalloc(cap);
	size_t o = 0;
	if (bglen) {
		memcpy(out + o, bg, bglen);
		o += bglen;
	}
	for (size_t i = 0; i < len; i++) {
		out[o++] = line[i];
		if (line[i] == '\x1b' && i + 1 < len && line[i + 1] == '[') {
			i += 1;
			out[o++] = line[i];
			while (i + 1 < len && line[i + 1] != 'm') {
				i++;
				out[o++] = line[i];
			}
			if (i + 1 < len && line[i + 1] == 'm') {
				i++;
				out[o++] = 'm';
				if (bglen) {
					memcpy(out + o, bg, bglen);
					o += bglen;
				}
			}
		}
		if (o + bglen + 8 >= cap) {
			cap *= 2;
			out = xrealloc(out, cap);
		}
	}
	if (o + 4 < cap) {
		out[o++] = '\x1b';
		out[o++] = '[';
		out[o++] = '0';
		out[o++] = 'm';
	}
	out[o] = '\0';
	return out;
}

static char *ansi_apply_char_diff(const char *line, const int16_t *ages, size_t age_len, int fade_cycles)
{
	if (!line || !*line)
		return xstrdup("");
	size_t len = strlen(line);
	size_t cap = len * 6 + 64;
	char *out = xmalloc(cap);
	size_t o = 0;
	size_t vis = 0;
	bool fg_set = false;
	int fg_r = 0;
	int fg_g = 0;
	int fg_b = 0;

	for (size_t i = 0; i < len; i++) {
		if (line[i] == '\x1b' && i + 1 < len && line[i + 1] == '[') {
			out[o++] = line[i];
			i++;
			out[o++] = line[i];
			size_t seq_start = i + 1;
			while (i + 1 < len && line[i + 1] != 'm') {
				i++;
				out[o++] = line[i];
			}
			if (i + 1 < len && line[i + 1] == 'm') {
				i++;
				out[o++] = 'm';
				ansi_update_fg_from_sgr(line + seq_start, i - seq_start, &fg_set, &fg_r, &fg_g, &fg_b);
			}
			continue;
		}

		size_t seq = utf8_seq_len((unsigned char)line[i]);
		if (seq > 1 && i + seq > len)
			seq = 1;

		bool highlight = false;
		int intensity = 0;
		if (vis < age_len && ages) {
			int16_t age = ages[vis];
			if (age < fade_cycles) {
				highlight = true;
				if (age < 0 && ansi_fade_in_frames > 0) {
					double ratio = (double)(ansi_fade_in_frames + age) / (double)ansi_fade_in_frames;
					if (ratio < 0.0)
						ratio = 0.0;
					if (ratio > 1.0)
						ratio = 1.0;
					intensity = (int)(ratio * (double)ansi_fade_max_brightness);
				} else if (ansi_fade_half_life && ansi_fade_half_life_frames > 0) {
					double ratio = pow(0.5, (double)age / (double)ansi_fade_half_life_frames);
					intensity = (int)(ratio * (double)ansi_fade_max_brightness);
				} else {
					intensity = (fade_cycles - age) * ansi_fade_max_brightness / fade_cycles;
				}
			}
		}
		if (highlight) {
			char bg[64];
			char fg[64];
			int restore_len = 0;
			char restore[80];
			int denom = ansi_fade_max_brightness > 0 ? ansi_fade_max_brightness : 1;
			double ratio = (double)intensity / (double)denom;
			if (ratio < 0.0)
				ratio = 0.0;
			if (ratio > 1.0)
				ratio = 1.0;
			int base_bg_r = ansi_default_bg_valid ? ansi_default_bg_r : 0;
			int base_bg_g = ansi_default_bg_valid ? ansi_default_bg_g : 0;
			int base_bg_b = ansi_default_bg_valid ? ansi_default_bg_b : 0;
			int bg_r = (int)(base_bg_r + (ansi_fade_bg_r - base_bg_r) * ratio + 0.5);
			int bg_g = (int)(base_bg_g + (ansi_fade_bg_g - base_bg_g) * ratio + 0.5);
			int bg_b = (int)(base_bg_b + (ansi_fade_bg_b - base_bg_b) * ratio + 0.5);
			int orig_fg_r = 0;
			int orig_fg_g = 0;
			int orig_fg_b = 0;
			bool have_orig_fg = false;
			if (fg_set) {
				orig_fg_r = fg_r;
				orig_fg_g = fg_g;
				orig_fg_b = fg_b;
				have_orig_fg = true;
			} else if (ansi_default_fg_valid) {
				orig_fg_r = ansi_default_fg_r;
				orig_fg_g = ansi_default_fg_g;
				orig_fg_b = ansi_default_fg_b;
				have_orig_fg = true;
			}
			double bg_luma = 0.2126 * bg_r + 0.7152 * bg_g + 0.0722 * bg_b;
			double fg_luma = have_orig_fg
				? (0.2126 * orig_fg_r + 0.7152 * orig_fg_g + 0.0722 * orig_fg_b)
				: 0.0;
			bool snap_fg = have_orig_fg && bg_luma < (fg_luma * 0.5);
			if (snap_fg) {
				(void)snprintf(fg, sizeof(fg), "\x1b[38;2;%d;%d;%dm", orig_fg_r, orig_fg_g, orig_fg_b);
			} else {
				(void)snprintf(fg, sizeof(fg), "\x1b[30m");
			}
			(void)snprintf(bg, sizeof(bg), "\x1b[48;2;%d;%d;%dm", bg_r, bg_g, bg_b);
			if (fg_set)
				restore_len = snprintf(restore, sizeof(restore), "\x1b[38;2;%d;%d;%dm\x1b[49m", fg_r, fg_g, fg_b);
			else
				restore_len = snprintf(restore, sizeof(restore), "\x1b[39m\x1b[49m");
			size_t fglen = strlen(fg);
			size_t bglen = strlen(bg);
			if (o + bglen + fglen + seq + (size_t)restore_len + 8 >= cap) {
				cap *= 2;
				out = xrealloc(out, cap);
			}
			memcpy(out + o, bg, bglen);
			o += bglen;
			memcpy(out + o, fg, fglen);
			o += fglen;
			memcpy(out + o, line + i, seq);
			o += seq;
			memcpy(out + o, restore, (size_t)restore_len);
			o += (size_t)restore_len;
		} else {
			if (o + seq + 1 >= cap) {
				cap *= 2;
				out = xrealloc(out, cap);
			}
			memcpy(out + o, line + i, seq);
			o += seq;
		}
		vis++;
		i += seq - 1;
		if (o + 32 >= cap) {
			cap *= 2;
			out = xrealloc(out, cap);
		}
	}
	out[o] = '\0';
	return out;
}

static size_t utf8_seq_len(unsigned char c)
{
	if (c < 0x80)
		return 1;
	if ((c & 0xE0) == 0xC0)
		return 2;
	if ((c & 0xF0) == 0xE0)
		return 3;
	if ((c & 0xF8) == 0xF0)
		return 4;
	return 1;
}

static size_t utf8_count_glyphs(const char *s)
{
	if (!s || !*s)
		return 0;
	size_t count = 0;
	size_t len = strlen(s);
	for (size_t i = 0; i < len; ) {
		size_t seq = utf8_seq_len((unsigned char)s[i]);
		if (seq > 1 && i + seq > len)
			seq = 1;
		i += seq;
		count++;
	}
	return count;
}

static bool parse_rgb_env(const char *value, int *r, int *g, int *b)
{
	if (!value || !*value)
		return false;
	long vals[3] = {0, 0, 0};
	int found = 0;
	const char *p = value;
	while (*p && found < 3) {
		while (*p && (*p < '0' || *p > '9'))
			p++;
		if (!*p)
			break;
		char *end = NULL;
		long v = strtol(p, &end, 10);
		if (end == p)
			break;
		if (v < 0)
			v = 0;
		if (v > 255)
			v = 255;
		vals[found++] = v;
		p = end;
	}
	if (found == 3) {
		*r = (int)vals[0];
		*g = (int)vals[1];
		*b = (int)vals[2];
		return true;
	}
	return false;
}

static void xterm256_to_rgb(int n, int *r, int *g, int *b)
{
	static const int base16[16][3] = {
		{0, 0, 0}, {205, 0, 0}, {0, 205, 0}, {205, 205, 0},
		{0, 0, 238}, {205, 0, 205}, {0, 205, 205}, {229, 229, 229},
		{127, 127, 127}, {255, 0, 0}, {0, 255, 0}, {255, 255, 0},
		{92, 92, 255}, {255, 0, 255}, {0, 255, 255}, {255, 255, 255}
	};
	if (n < 0)
		n = 0;
	if (n > 255)
		n = 255;
	if (n < 16) {
		*r = base16[n][0];
		*g = base16[n][1];
		*b = base16[n][2];
		return;
	}
	if (n >= 232) {
		int gray = 8 + (n - 232) * 10;
		*r = gray;
		*g = gray;
		*b = gray;
		return;
	}
	n -= 16;
	int ir = n / 36;
	int ig = (n / 6) % 6;
	int ib = n % 6;
	int steps[6] = {0, 95, 135, 175, 215, 255};
	*r = steps[ir];
	*g = steps[ig];
	*b = steps[ib];
}

static void ansi_update_fg_from_sgr(const char *seq, size_t len, bool *fg_set, int *fr, int *fg, int *fb)
{
	if (!seq || len == 0)
		return;
	int params[32];
	int pcount = 0;
	int cur = -1;
	for (size_t i = 0; i < len && pcount < (int)(sizeof(params) / sizeof(params[0])); i++) {
		char c = seq[i];
		if (c >= '0' && c <= '9') {
			if (cur < 0)
				cur = 0;
			cur = cur * 10 + (c - '0');
		} else if (c == ';' || c == ':') {
			if (cur < 0)
				params[pcount++] = 0;
			else
				params[pcount++] = cur;
			cur = -1;
		}
	}
	if (cur >= 0 && pcount < (int)(sizeof(params) / sizeof(params[0])))
		params[pcount++] = cur;
	if (pcount == 0) {
		params[pcount++] = 0;
	}

	for (int i = 0; i < pcount; i++) {
		int code = params[i];
		if (code == 0 || code == 39) {
			*fg_set = false;
			continue;
		}
		if (code >= 30 && code <= 37) {
			xterm256_to_rgb(code - 30, fr, fg, fb);
			*fg_set = true;
			continue;
		}
		if (code >= 90 && code <= 97) {
			xterm256_to_rgb(code - 90 + 8, fr, fg, fb);
			*fg_set = true;
			continue;
		}
		if (code == 38) {
			if (i + 1 < pcount && params[i + 1] == 2 && i + 4 < pcount) {
				*fr = params[i + 2];
				*fg = params[i + 3];
				*fb = params[i + 4];
				*fg_set = true;
				i += 4;
				continue;
			}
			if (i + 1 < pcount && params[i + 1] == 5 && i + 2 < pcount) {
				xterm256_to_rgb(params[i + 2], fr, fg, fb);
				*fg_set = true;
				i += 2;
				continue;
			}
		}
	}
}

static void load_watch_prefs(void)
{
	const char *home = getenv("HOME");
	char homebuf[PATH_MAX];
	if ((!home || !*home)) {
		struct passwd *pw = getpwuid(getuid());
		if (pw && pw->pw_dir) {
			snprintf(homebuf, sizeof(homebuf), "%s", pw->pw_dir);
			home = homebuf;
		}
	}
	char path[PATH_MAX];
	const char *candidates[1];
	int idx = 0;
	if (home && *home) {
		snprintf(path, sizeof(path), "%s/.watchrc", home);
		candidates[idx++] = path;
	}

	const char *cfg = NULL;
	for (int i = 0; i < idx; i++) {
		if (candidates[i] && access(candidates[i], R_OK) == 0) {
			cfg = candidates[i];
			break;
		}
	}

	if (!cfg)
		return;

	FILE *fp = fopen(cfg, "r");
	if (!fp)
		return;

	char line[512];
	while (fgets(line, sizeof(line), fp)) {
		char *p = line;
		while (*p == ' ' || *p == '\t')
			p++;
		if (*p == '\0' || *p == '\n' || *p == '#')
			continue;
		char *eq = strchr(p, '=');
		if (!eq)
			continue;
		*eq = '\0';
		char *key = p;
		char *val = eq + 1;
		char *end = key + strlen(key);
		while (end > key && (end[-1] == ' ' || end[-1] == '\t'))
			*--end = '\0';
		while (*val == ' ' || *val == '\t')
			val++;
		end = val + strlen(val);
		while (end > val && (end[-1] == '\n' || end[-1] == '\r' || end[-1] == ' ' || end[-1] == '\t'))
			*--end = '\0';

		if (*key == '\0' || *val == '\0')
			continue;

		if (strncasecmp(key, "watch_", 6) == 0)
			key += 6;

		if (strcasecmp(key, "fade") == 0) {
			double v = strtod(val, NULL);
			if (v > 0.0 && v < 1000.0)
				ansi_fade_seconds = v;
		} else if (strcasecmp(key, "half_life") == 0) {
			if (strcmp(val, "1") == 0 || strcasecmp(val, "true") == 0)
				ansi_fade_half_life = true;
		} else if (strcasecmp(key, "fps") == 0) {
			long v = strtol(val, NULL, 10);
			if (v > 0 && v <= 60)
				ansi_fade_fps = (int)v;
		} else if (strcasecmp(key, "fade_max") == 0) {
			long v = strtol(val, NULL, 10);
			if (v < 0)
				v = 0;
			if (v > 255)
				v = 255;
			ansi_fade_max_brightness = (int)v;
		} else if (strcasecmp(key, "fade_in") == 0) {
			double v = strtod(val, NULL);
			if (v > 0.0 && v < 1000.0)
				ansi_fade_in_seconds = v;
		} else if (strcasecmp(key, "fade_bg") == 0) {
			(void)parse_rgb_env(val, &ansi_fade_bg_r, &ansi_fade_bg_g, &ansi_fade_bg_b);
		}
	}
	fclose(fp);
}

static void load_default_fg_from_env(void)
{
	const char *cfg = getenv("COLORFGBG");
	if (!cfg || !*cfg)
		return;
	char buf[64];
	snprintf(buf, sizeof(buf), "%s", cfg);
	char *sep = strpbrk(buf, ";:,");
	if (!sep)
		return;
	*sep = '\0';
	char *end = NULL;
	long fg = strtol(buf, &end, 10);
	if (end == buf || fg < 0 || fg > 255)
		return;
	xterm256_to_rgb((int)fg, &ansi_default_fg_r, &ansi_default_fg_g, &ansi_default_fg_b);
	ansi_default_fg_valid = true;
}

static void query_default_fg(void)
{
	if (ansi_default_fg_valid)
		return;
	(void)!write(STDOUT_FILENO, "\x1b]10;?\x07", 8);

	char buf[128];
	size_t n = 0;
	struct timeval tv;
	fd_set rfds;
	for (;;) {
		FD_ZERO(&rfds);
		FD_SET(STDIN_FILENO, &rfds);
		tv.tv_sec = 0;
		tv.tv_usec = 50000;
		int r = select(STDIN_FILENO + 1, &rfds, NULL, NULL, &tv);
		if (r <= 0)
			break;
		if (!FD_ISSET(STDIN_FILENO, &rfds))
			break;
		ssize_t got = read(STDIN_FILENO, buf + n, sizeof(buf) - 1 - n);
		if (got <= 0)
			break;
		n += (size_t)got;
		buf[n] = '\0';
		if (strchr(buf, '\a') || strstr(buf, "\x1b\\"))
			break;
		if (n >= sizeof(buf) - 1)
			break;
	}

	char *rgb = strstr(buf, "rgb:");
	if (!rgb)
		return;
	int r = 0, g = 0, b = 0;
	if (parse_rgb_response(rgb, &r, &g, &b)) {
		ansi_default_fg_r = r;
		ansi_default_fg_g = g;
		ansi_default_fg_b = b;
		ansi_default_fg_valid = true;
	}
}

static void query_default_bg(void)
{
	(void)!write(STDOUT_FILENO, "\x1b]11;?\x07", 8);

	char buf[128];
	size_t n = 0;
	struct timeval tv;
	fd_set rfds;
	for (;;) {
		FD_ZERO(&rfds);
		FD_SET(STDIN_FILENO, &rfds);
		tv.tv_sec = 0;
		tv.tv_usec = 50000;
		int r = select(STDIN_FILENO + 1, &rfds, NULL, NULL, &tv);
		if (r <= 0)
			break;
		if (!FD_ISSET(STDIN_FILENO, &rfds))
			break;
		ssize_t got = read(STDIN_FILENO, buf + n, sizeof(buf) - 1 - n);
		if (got <= 0)
			break;
		n += (size_t)got;
		buf[n] = '\0';
		if (strchr(buf, '\a') || strstr(buf, "\x1b\\"))
			break;
		if (n >= sizeof(buf) - 1)
			break;
	}

	char *rgb = strstr(buf, "rgb:");
	if (!rgb) {
		log_watch_debug("bg", 0, 0, 0, false);
		return;
	}
	int r = 0, g = 0, b = 0;
	if (parse_rgb_response(rgb, &r, &g, &b)) {
		ansi_default_bg_r = r;
		ansi_default_bg_g = g;
		ansi_default_bg_b = b;
		ansi_default_bg_valid = true;
		log_watch_debug("bg", r, g, b, true);
		return;
	}
	log_watch_debug("bg", 0, 0, 0, false);
}

static bool parse_rgb_response(const char *rgb, int *r, int *g, int *b)
{
	const char *p = strchr(rgb, ':');
	if (!p)
		return false;
	p++;
	int vals[3] = {0, 0, 0};
	for (int i = 0; i < 3; i++) {
		int v = 0;
		int digits = 0;
		while (*p && *p != '/' && digits < 4) {
			char c = *p;
			int d = -1;
			if (c >= '0' && c <= '9')
				d = c - '0';
			else if (c >= 'a' && c <= 'f')
				d = 10 + (c - 'a');
			else if (c >= 'A' && c <= 'F')
				d = 10 + (c - 'A');
			else
				break;
			v = (v << 4) | d;
			digits++;
			p++;
		}
		if (digits == 0)
			return false;
		if (digits <= 2)
			vals[i] = v;
		else {
			int maxv = (1 << (digits * 4)) - 1;
			vals[i] = (v * 255 + maxv / 2) / maxv;
		}
		if (*p == '/')
			p++;
	}
	*r = vals[0];
	*g = vals[1];
	*b = vals[2];
	return true;
}

static void log_watch_debug(const char *label, int r, int g, int b, bool ok)
{
	FILE *fp = fopen("/tmp/watch-debug.log", "a");
	if (!fp)
		return;
	fprintf(fp, "%s default_%s %s rgb=%d,%d,%d\n", program_invocation_short_name, label,
		ok ? "ok" : "fail", r, g, b);
	fclose(fp);
}

static void log_watch_settings(void)
{
	FILE *fp = fopen("/tmp/watch-debug.log", "a");
	if (!fp)
		return;
	fprintf(fp,
		"%s settings fade=%.3f half_life=%d fps=%d fade_in=%.3f fade_max=%d fade_bg=%d,%d,%d\n",
		program_invocation_short_name,
		ansi_fade_seconds,
		ansi_fade_half_life ? 1 : 0,
		ansi_fade_fps,
		ansi_fade_in_seconds,
		ansi_fade_max_brightness,
		ansi_fade_bg_r,
		ansi_fade_bg_g,
		ansi_fade_bg_b);
	fclose(fp);
}

static int16_t *build_fadein_ages(const char *prev, const char *next, size_t prev_glyphs)
{
	int16_t *ages = xcalloc(prev_glyphs, sizeof(*ages));
	size_t plen = prev ? strlen(prev) : 0;
	size_t nlen = next ? strlen(next) : 0;
	size_t pi = 0;
	size_t ni = 0;
	size_t g = 0;
	while (pi < plen && g < prev_glyphs) {
		size_t pseq = utf8_seq_len((unsigned char)prev[pi]);
		if (pseq > 1 && pi + pseq > plen)
			pseq = 1;
		bool ch = false;
		size_t nseq = 0;
		if (!next || ni >= nlen) {
			ch = true;
		} else {
			nseq = utf8_seq_len((unsigned char)next[ni]);
			if (nseq > 1 && ni + nseq > nlen)
				nseq = 1;
			if (pseq != nseq || memcmp(prev + pi, next + ni, pseq) != 0)
				ch = true;
		}
		if (ch)
			ages[g] = (ansi_fade_in_frames > 0) ? (int16_t)-ansi_fade_in_frames : 0;
		else
			ages[g] = (int16_t)ansi_fade_cycles;
		pi += pseq;
		if (!ch && nseq > 0)
			ni += nseq;
		else if (ni < nlen && nseq > 0)
			ni += nseq;
		g++;
	}
	return ages;
}

static char *ansi_truncate_visible(const char *line, int cols)
{
	if (!line || !*line || cols <= 0)
		return xstrdup("");
	size_t len = strlen(line);
	size_t cap = len + 16;
	char *out = xmalloc(cap);
	size_t o = 0;
	int col = 0;
	mbstate_t st;
	memset(&st, 0, sizeof(st));

	for (size_t i = 0; i < len && col < cols; ) {
		if (line[i] == '\x1b' && i + 1 < len && line[i + 1] == '[') {
			if (o + 2 >= cap) {
				cap *= 2;
				out = xrealloc(out, cap);
			}
			out[o++] = line[i++];
			out[o++] = line[i++];
			while (i < len) {
				if (o + 1 >= cap) {
					cap *= 2;
					out = xrealloc(out, cap);
				}
				out[o++] = line[i];
				if (line[i] == 'm') {
					i++;
					break;
				}
				i++;
			}
			continue;
		}

		size_t seq = utf8_seq_len((unsigned char)line[i]);
		if (seq > 1 && i + seq > len)
			seq = 1;
		wchar_t wc;
		size_t m = mbrtowc(&wc, line + i, seq, &st);
		int w = 1;
		if (m == (size_t)-1 || m == (size_t)-2) {
			memset(&st, 0, sizeof(st));
			seq = 1;
			w = 1;
		} else {
			int wcw = wcwidth(wc);
			w = wcw < 0 ? 1 : wcw;
		}
		if (col + w > cols)
			break;
		if (o + seq + 1 >= cap) {
			cap *= 2;
			out = xrealloc(out, cap);
		}
		memcpy(out + o, line + i, seq);
		o += seq;
		i += seq;
		col += w;
	}
	out[o] = '\0';
	return out;
}

static bool ansi_has_active_fade(void)
{
	for (int row = 0; row < ansi_prev_count; row++) {
		if (!ansi_char_age[row])
			continue;
		for (size_t i = 0; i < ansi_char_age_len[row]; i++) {
			if (ansi_char_age[row][i] < ansi_fade_cycles)
				return true;
		}
	}
	return false;
}

static void ansi_render_current(int start_row)
{
	for (int row = 0; row < ansi_prev_count; row++) {
		const char *line = ansi_prev_lines[row] ? ansi_prev_lines[row] : "";
		char *out_line = NULL;
		if ((flags & WATCH_DIFF) && ansi_char_age[row]) {
			out_line = ansi_apply_char_diff(line, ansi_char_age[row], ansi_char_age_len[row], ansi_fade_cycles);
		} else {
			out_line = xstrdup(line);
		}
		ansi_write_line(start_row + row, out_line);
		free(out_line);
	}
}
static void ansi_reset_prev_buffers(int count)
{
	for (int i = 0; i < ansi_prev_count; i++) {
		free(ansi_prev_lines ? ansi_prev_lines[i] : NULL);
		free(ansi_prev_plain ? ansi_prev_plain[i] : NULL);
		free(ansi_char_age ? ansi_char_age[i] : NULL);
		free(ansi_pending_lines ? ansi_pending_lines[i] : NULL);
		free(ansi_pending_plain ? ansi_pending_plain[i] : NULL);
		free(ansi_pending_ages ? ansi_pending_ages[i] : NULL);
	}
	free(ansi_prev_lines);
	free(ansi_prev_plain);
	free(ansi_line_age);
	free(ansi_line_seen);
	free(ansi_char_age);
	free(ansi_char_age_len);
	free(ansi_pending_lines);
	free(ansi_pending_plain);
	free(ansi_pending_ages);
	free(ansi_pending_age_len);
	ansi_pending_active = false;
	ansi_pending_frames = 0;
	ansi_prev_lines = xcalloc((size_t)count, sizeof(*ansi_prev_lines));
	ansi_prev_plain = xcalloc((size_t)count, sizeof(*ansi_prev_plain));
	ansi_line_age = xcalloc((size_t)count, sizeof(*ansi_line_age));
	ansi_line_seen = xcalloc((size_t)count, sizeof(*ansi_line_seen));
	ansi_char_age = xcalloc((size_t)count, sizeof(*ansi_char_age));
	ansi_char_age_len = xcalloc((size_t)count, sizeof(*ansi_char_age_len));
	ansi_pending_lines = xcalloc((size_t)count, sizeof(*ansi_pending_lines));
	ansi_pending_plain = xcalloc((size_t)count, sizeof(*ansi_pending_plain));
	ansi_pending_ages = xcalloc((size_t)count, sizeof(*ansi_pending_ages));
	ansi_pending_age_len = xcalloc((size_t)count, sizeof(*ansi_pending_age_len));
	ansi_prev_count = count;
}

static char **ansi_read_lines(FILE *p, int max_lines, int *out_count)
{
	size_t cap = 8192;
	size_t len = 0;
	char *buf = xmalloc(cap);
	size_t n;
	char chunk[4096];
	while ((n = fread(chunk, 1, sizeof(chunk), p)) > 0) {
		if (len + n + 1 > cap) {
			while (len + n + 1 > cap)
				cap *= 2;
			buf = xrealloc(buf, cap);
		}
		memcpy(buf + len, chunk, n);
		len += n;
	}
	buf[len] = '\0';

	if (len > 0) {
		size_t w = 0;
		for (size_t r = 0; r < len; r++) {
			if (buf[r] == '\r') {
				if (r + 1 < len && buf[r + 1] == '\n') {
					continue;
				}
				buf[w++] = '\n';
				continue;
			}
			buf[w++] = buf[r];
		}
		buf[w] = '\0';
		len = w;
	}

	char **lines = xcalloc((size_t)max_lines, sizeof(*lines));
	int count = 0;
	size_t start = 0;
	for (size_t i = 0; i <= len && count < max_lines; i++) {
		if (buf[i] == '\n' || buf[i] == '\0') {
			size_t l = i - start;
			char *line = xmalloc(l + 1);
			memcpy(line, buf + start, l);
			line[l] = '\0';
			lines[count++] = line;
			start = i + 1;
		}
	}
	free(buf);
	*out_count = count;
	return lines;
}


static uf8 rgb_to_ansi256(int r, int g, int b)
{
	if (r == g && g == b) {
		if (r < 8)
			return 16;
		if (r > 248)
			return 231;
		return 232 + (r - 8) / 10;
	}
	int ir = (r * 5 + 127) / 255;
	int ig = (g * 5 + 127) / 255;
	int ib = (b * 5 + 127) / 255;
	return 16 + 36 * ir + 6 * ig + ib;
}


static void init_ansi_colors(void)
{
	const short ncurses_colors[] = {
		-1, COLOR_BLACK, COLOR_RED, COLOR_GREEN, COLOR_YELLOW,
		COLOR_BLUE, COLOR_MAGENTA, COLOR_CYAN, COLOR_WHITE
	};
	nr_of_colors = sizeof(ncurses_colors) / sizeof(*ncurses_colors);

	more_colors = (COLORS >= 16) && (COLOR_PAIRS >= 16 * 16);

	// Initialize ncurses colors. -1 is terminal default
	// 0-7 are auto created standard colors initialized by ncurses
	if (more_colors) {
		// Initialize using ANSI SGR 8-bit specified colors
		// 8-15 are bright colors
		init_color(8, 333, 333, 333);  // Bright black
		init_color(9, 1000, 333, 333);  // Bright red
		init_color(10, 333, 1000, 333);  // Bright green
		init_color(11, 1000, 1000, 333);  // Bright yellow
		init_color(12, 333, 333, 1000);  // Bright blue
		init_color(13, 1000, 333, 1000);  // Bright magenta
		init_color(14, 333, 1000, 1000);  // Bright cyan
		// Often ncurses is built with only 256 colors, so lets
		// stop here - so we can support the -1 terminal default
		//init_color(15, 1000, 1000, 1000);  // Bright white
		nr_of_colors += 7;
	}
#ifdef WITH_WATCH8BIT
        if (COLORS >= 256 && COLOR_PAIRS >= 65536)
        {
            int red,green,blue;
            int code, r,g,b;
            // 16 to 231 are a 6x6x6 color cube
            for (red=0; red<6; red++)
                for(green=0; green<6; green++)
                    for(blue=0; blue<6; blue++) {
                        code = 16 + (red * 36) + (green * 6) + blue;
                        r = g = b = 0;
                        if (red > 0)
                            r = (red * 40 + 55) * 1000 / 256;
                        if (green > 0)
                            g = (green * 40 + 55) * 1000 / 256;
                        if (blue > 0)
                            b = (blue * 40 + 55) * 1000 / 256;
                        init_extended_color(code, r, g, b);
                        nr_of_colors++;
                    }
            for (red=0; red<24; red++) {
                code = 232 + red;
                r = (red * 10 + 8) * 1000 / 256;
                init_extended_color(code, r, r, r);
                nr_of_colors++;
            }
        }
#endif /*8bit*/
	// Initialize all color pairs with ncurses
	for (bg_col = 0; bg_col < nr_of_colors; bg_col++)
		for (fg_col = 0; fg_col < nr_of_colors; fg_col++)
#ifdef WITH_WATCH8BIT
			init_extended_pair(bg_col * nr_of_colors + fg_col + 1, fg_col - 1, bg_col - 1);
#else
			init_pair(bg_col * nr_of_colors + fg_col + 1, fg_col - 1, bg_col - 1);
#endif

	reset_ansi();
}



static uf8 process_ansi_color_escape_sequence(char **const escape_sequence) {
	// process SGR ANSI color escape sequence
	// Eg 8-bit
	// 38;5;⟨n⟩  (set fg color to n)
	// 48;5;⟨n⟩  (set bg color to n)
	//
	// Eg 24-bit (mapped to nearest 256-color entry)
	// ESC[ 38;2;⟨r⟩;⟨g⟩;⟨b⟩ m Select RGB foreground color
	// ESC[ 48;2;⟨r⟩;⟨g⟩;⟨b⟩ m Select RGB background color

	if (!escape_sequence || !*escape_sequence)
		return 0; /* avoid NULLPTR dereference, return "not understood" */

	if ((*escape_sequence)[0] != ';')
		return 0; /* not understood */

	if ((*escape_sequence)[1] == '5') {
		// 8 bit! ANSI specifies a predefined set of 256 colors here.
		if ((*escape_sequence)[2] != ';')
			return 0; /* not understood */
		long num = strtol((*escape_sequence) + 3, escape_sequence, 10);
		if (num >= 0 && num <= 7) {
			// 0-7 are standard colors  same as SGR 30-37
			return num + 1;
		}
		if (num >= 8 && num <= 15) {
			// 8-15 are standard colors  same as SGR 90-97
			 return more_colors ? num + 1 : num - 8 + 1;
		}
		// 16-231:  6 × 6 × 6 cube (216 colors): 16 + 36 × r + 6 × g + b
		//                                       (0 ≤ r, g, b ≤ 5)
		// 232-255:  grayscale from black to white in 24 steps
#ifdef WITH_WATCH8BIT
		if (num > 15 && num < 256)
			return more_colors ? num + 1 : 0;
#endif
	}

	if ((*escape_sequence)[1] == '2') {
		if ((*escape_sequence)[2] != ';')
			return 0; /* not understood */
		char *p = (*escape_sequence) + 3;
		long r = strtol(p, &p, 10);
		if (*p != ';')
			return 0; /* not understood */
		long g = strtol(p + 1, &p, 10);
		if (*p != ';')
			return 0; /* not understood */
		long b = strtol(p + 1, escape_sequence, 10);
		if (r < 0 || r > 255 || g < 0 || g > 255 || b < 0 || b > 255)
			return 0; /* not understood */

		uf8 num = rgb_to_ansi256((int)r, (int)g, (int)b);
		if (num <= 7)
			return num + 1;
		if (num <= 15)
			return more_colors ? num + 1 : num - 8 + 1;
#ifdef WITH_WATCH8BIT
		if (num < 256)
			return more_colors ? num + 1 : 0;
#endif
	}

	return 0; /* not understood */
}



static bool set_ansi_attribute(const int attrib, char** escape_sequence)
{
	if (!(flags & WATCH_COLOR))
		return true;

	switch (attrib) {
	case -1:	/* restore last settings */
		break;
	case 0:		/* restore default settings */
		reset_ansi();
		break;
	case 1:		/* set bold / increased intensity */
		attributes |= A_BOLD;
		break;
	case 2:		/* set decreased intensity (if supported) */
		attributes |= A_DIM;
		break;
#ifdef A_ITALIC
	case 3:		/* set italic (if supported) */
		attributes |= A_ITALIC;
		break;
#endif
	case 4:		/* set underline */
		attributes |= A_UNDERLINE;
		break;
	case 5:		/* set blinking */
		attributes |= A_BLINK;
		break;
	case 7:		/* set inversed */
		attributes |= A_REVERSE;
		break;
	case 21:	/* unset bold / increased intensity */
		attributes &= ~A_BOLD;
		break;
	case 22:	/* unset bold / any intensity modifier */
		attributes &= ~(A_BOLD | A_DIM);
		break;
#ifdef A_ITALIC
	case 23:	/* unset italic */
		attributes &= ~A_ITALIC;
		break;
#endif
	case 24:	/* unset underline */
		attributes &= ~A_UNDERLINE;
		break;
	case 25:	/* unset blinking */
		attributes &= ~A_BLINK;
		break;
	case 27:	/* unset inversed */
		attributes &= ~A_REVERSE;
		break;
    case 38:
        fg_col = process_ansi_color_escape_sequence(escape_sequence);
        if (fg_col == 0) {
            return false; /* not understood */
        }
        break;
	case 39:
		fg_col = 0;
		break;
    case 48:
        bg_col = process_ansi_color_escape_sequence(escape_sequence);
        if (bg_col == 0) {
            return false; /* not understood */
        }
        break;
    case 49:
        bg_col = 0;
        break;
	default:
		if (attrib >= 30 && attrib <= 37) {	/* set foreground color */
			fg_col = attrib - 30 + 1;
		} else if (attrib >= 40 && attrib <= 47) { /* set background color */
			bg_col = attrib - 40 + 1;
		} else if (attrib >= 90 && attrib <= 97) { /* set bright fg color */
			fg_col = more_colors ? attrib - 90 + 9 : attrib - 90 + 1;
		} else if (attrib >= 100 && attrib <= 107) { /* set bright bg color */
			bg_col = more_colors ? attrib - 100 + 9 : attrib - 100 + 1;
		} else {
			return false; /* Not understood */
		}
	}
    int c = bg_col * nr_of_colors + fg_col + 1;
    wattr_set(mainwin, attributes, 0, &c);
    return true;
}



static void process_ansi(FILE * fp)
{
	if (!(flags & WATCH_COLOR))
		return;

	int i, c;
	char buf[MAX_ANSIBUF];
	char *numstart, *endptr;
	int ansi_attribute;

	c = getc(fp);

	if (c == '(') {
		c = getc(fp);
		c = getc(fp);
	}
	if (c != '[') {
		ungetc(c, fp);
		return;
	}
	for (i = 0; i < MAX_ANSIBUF; i++) {
		c = getc(fp);
		/* COLOUR SEQUENCE ENDS in 'm' */
		if (c == 'm') {
			buf[i] = '\0';
			break;
		}
		if ((c < '0' || c > '9') && c != ';') {
			return;
		}
		assert(c >= 0 && c <= SCHAR_MAX);
		buf[i] = c;
	}
	/*
	 * buf now contains a semicolon-separated list of decimal integers,
	 * each indicating an attribute to apply.
	 * For example, buf might contain "0;1;31", derived from the color
	 * escape sequence "<ESC>[0;1;31m". There can be 1 or more
	 * attributes to apply, but typically there are between 1 and 3.
	 */

    /* Special case of <ESC>[m */
    if (buf[0] == '\0')
        set_ansi_attribute(0, NULL);

    for (endptr = numstart = buf; *endptr != '\0'; numstart = endptr + 1) {
        ansi_attribute = strtol(numstart, &endptr, 10);
        if (!set_ansi_attribute(ansi_attribute, &endptr))
            break;
        if (numstart == endptr)
            set_ansi_attribute(0, NULL); /* [m treated as [0m */
    }
}



static inline watch_usec_t get_time_usec(void)
{
	struct timeval now;
#if defined(HAVE_CLOCK_GETTIME) && defined(_POSIX_TIMERS)
	struct timespec ts;
	if (0 > clock_gettime(CLOCK_MONOTONIC, &ts))
		endwin_xerr(1, "clock_gettime(CLOCK_MONOTONIC)");
	TIMESPEC_TO_TIMEVAL(&now, &ts);
#else
	gettimeofday(&now, NULL);
#endif /* HAVE_CLOCK_GETTIME */
	return USECS_PER_SEC * now.tv_sec + now.tv_usec;
}



static void screenshot(void) {
	static time_t last;
	static uf8 last_nr;
	static char *dumpfile;
	static size_t dumpfile_mark;
	static uf8 dumpfile_avail = 128;

	if (! dumpfile) {
		dumpfile_mark = strlen(shotsdir);  // can be empty
		if (SIZE_MAX - dumpfile_mark < dumpfile_avail)
			endwin_error(1, ENAMETOOLONG, "%s", shotsdir);
		dumpfile = xmalloc(dumpfile_mark + dumpfile_avail);  // never freed
		if (dumpfile_mark) {
			memcpy(dumpfile, shotsdir, dumpfile_mark);
			if (dumpfile[dumpfile_mark-1] != '/') {
				dumpfile[dumpfile_mark++] = '/';
				--dumpfile_avail;
			}
		}
		memcpy(dumpfile+dumpfile_mark, "watch_", 6);
		dumpfile_mark += 6;
		dumpfile_avail -= 6;
	}

	const time_t now = time(NULL);
	if (! strftime(dumpfile+dumpfile_mark, dumpfile_avail, "%Y%m%d-%H%M%S", localtime(&now))) {
		assert(false);
		dumpfile[dumpfile_mark] = '\0';
	}
	if (now == last) {
		const uf8 l = strlen(dumpfile+dumpfile_mark);
		assert(dumpfile_avail - l >= 5);
		snprintf(dumpfile+dumpfile_mark+l, dumpfile_avail-l, "-%03" PRIuFAST8, last_nr);
		assert(last_nr < UINT_FAST8_MAX);
		if (last_nr < UINT_FAST8_MAX)
			++last_nr;
	}
	else {
		last = now;
		last_nr = 0;
	}

	const int f = open(dumpfile, O_WRONLY|O_CREAT|O_EXCL, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
	if (f == -1)
		endwin_xerr(1, "open(%s)", dumpfile);

	int bufsize = 0;  // int because of mvinnstr()
#ifdef WITH_WATCH8BIT
	if ( INT_MAX / width >= CCHARW_MAX &&
	     MB_CUR_MAX <= INT_MAX &&
	     INT_MAX / (width*CCHARW_MAX) >= (int)MB_CUR_MAX &&
	     width * CCHARW_MAX * MB_CUR_MAX < INT_MAX
	   ) {
		bufsize = width*CCHARW_MAX*MB_CUR_MAX + 1;
	}
#else
	if (width < INT_MAX)
		bufsize = width + 1;
#endif
	if (! bufsize || (uintmax_t)bufsize > SIZE_MAX)
		endwin_error(1, EOVERFLOW, "%s(%s)", __func__, dumpfile);
	char *const buf = xmalloc(bufsize);

	int yin, xout, tmpy, tmpx;
        getyx(mainwin, tmpy, tmpx);
	for (int y=0; y<tmpy; ++y) {
		yin = mvwinnstr(mainwin, y, 0, buf, bufsize-1);
		if (yin == ERR)  // screen resized
			yin = 0;
		buf[yin] = '\n';
		for (int x=0; x<yin+1; x+=xout) {
			xout = write(f, buf+x, (yin+1)-x);
			if (xout == -1)
				endwin_xerr(1, "write(%s)", dumpfile);
		}
	}
        wmove(mainwin, tmpy, tmpx);
	free(buf);

	if (close(f) == -1)
		endwin_xerr(1, "close(%s)", dumpfile);

	if (screen_size_changed)
		endwin_error(1, ECANCELED, "%s(%s)", __func__, dumpfile);
}



static void output_header(
        WINDOW *hdrwin // Header window
        )
{
	if (flags & WATCH_NOTITLE)
		return;

	static char *lheader;
	static int lheader_len;
#ifdef WITH_WATCH8BIT
	static wchar_t *wlheader;
	static int wlheader_wid;
#endif

	static char rheader[256+128];  // hostname and timestamp
	static int rheader_lenmid;  // just before timestamp
	int rheader_len;
#ifdef WITH_WATCH8BIT
	wchar_t *wrheader;
	int wrheader_wid;

	static wchar_t *wcommand;
	static size_t wcommand_len;
	static int wcommand_wid;

	static sf8 ellipsis_wid;
#endif

	if (! lheader_len) {
		// my glibc says HOST_NAME_MAX is 64, but as soon as it updates it to be
		// at least POSIX.1-2001-compliant, it will be one of: 255, very large,
		// unspecified
		if (gethostname(rheader, 256))
			rheader[0] = '\0';
		rheader[255] = '\0';
		rheader_lenmid = strlen(rheader);
		rheader[rheader_lenmid++] = ':';
		rheader[rheader_lenmid++] = ' ';

		// never freed for !WATCH8BIT
		lheader_len = asprintf(&lheader, _("Every %.1fs: "), interval_real);
		if (lheader_len == -1)
			endwin_xerr(1, "%s()", __func__);
#ifdef WITH_WATCH8BIT
		// never freed
		wlheader_wid = mbswidth(lheader, &wlheader);
		if (wlheader_wid == -1) {
			wlheader = L"";
			wlheader_wid = 0;
		}
		free(lheader);

		// never freed
		wcommand_wid = mbswidth(command, &wcommand);
		if (wcommand_wid == -1) {
			wcommand = L"";
			wcommand_wid = 0;
		}
		wcommand_len = wcslen(wcommand);

		ellipsis_wid = wcwidth(L'\u2026');
#endif
	}

	// TODO: a gettext string for rheader no longer used
	const time_t t = time(NULL);
	rheader_len = rheader_lenmid;
	rheader_len += strftime(rheader+rheader_lenmid, sizeof(rheader)-rheader_lenmid, "%c", localtime(&t));
	if (rheader_len == rheader_lenmid)
		rheader[rheader_len] = '\0';
#ifdef WITH_WATCH8BIT
	wrheader_wid = mbswidth(rheader, &wrheader);
	if (wrheader_wid == -1) {
		wrheader = xmalloc(sizeof(*wrheader));
		wrheader[0] = L'\0';
		wrheader_wid = 0;
	}
#endif

	if (first_screen) {
		wmove(hdrwin, 0, 0);
		wclrtoeol(hdrwin);
	}

	/* left justify interval and command, right justify hostname and time,
	 * clipping all to fit window width
	 *
	 * the rules:
	 *   width < rhlen : print nothing
	 *   width < rhlen + hlen + 1: print hostname, ts
	 *   width = rhlen + hlen + 1: print header, hostname, ts
	 *   width < rhlen + hlen + 4: print header, ..., hostname, ts
	 *   width < rhlen + hlen + wcommand_columns: print header,
	 *                           truncated wcommand, ..., hostname, ts
	 *   width > "": print header, wcomand, hostname, ts
	 * this is slightly different from how it used to be */

// (w)command_* can be large, *header_* are relatively small
#ifdef WITH_WATCH8BIT
	if (width >= wrheader_wid) {
		mvwaddwstr(hdrwin, 0, width - wrheader_wid, wrheader);
		const int avail4cmd = width - wlheader_wid - wrheader_wid;
		if (avail4cmd >= 0) {
			mvwaddwstr(hdrwin,0, 0, wlheader);
			// All of cmd fits, +1 for delimiting space
			if (avail4cmd > wcommand_wid)
				waddwstr(hdrwin, wcommand);
			// Else print truncated cmd (to 0 chars, possibly) + ellipsis. If
			// there's too little space even for the ellipsis, print nothing.
			else if (avail4cmd > ellipsis_wid) {
				assert(wcommand_len > 0);
				int newwcmdwid;
				size_t newwcmdlen = wcommand_len;
				// from the back
				do newwcmdwid = wcswidth(wcommand, --newwcmdlen);
				while (newwcmdwid > avail4cmd-ellipsis_wid-1);
				waddnwstr(hdrwin, wcommand, newwcmdlen&INT_MAX);
				waddwstr(hdrwin, L"\u2026");
			}
		}
	}
	free(wrheader);
#else
	if (width >= rheader_len) {
		mvwaddstr(hdrwin, 0, width - rheader_len, rheader);
		const int avail4cmd = width - lheader_len - rheader_len;
		if (avail4cmd >= 0) {
			mvwaddstr(hdrwin, 0, 0, lheader);
			if ((uintmax_t)avail4cmd > command_len)
				waddstr(hdrwin, command);
			else if (avail4cmd > 3) {
				waddnstr(hdrwin, command, avail4cmd - 3 - 1);
				waddstr(hdrwin, "...");
			}
		}
	}
#endif
}



static void output_lowheader_pre(
        WINDOW *hdrwin
        )
{
	if (flags & WATCH_NOTITLE)
		return;

	wmove(hdrwin, 1, 0);
	wclrtoeol(hdrwin);
}

static void output_lowheader(
        WINDOW *hdrwin,
        watch_usec_t span,
        uint8_t exitcode)
{
	char s[64];
	int skip;

	if (flags & WATCH_NOTITLE)
		return;

	wmove(hdrwin, 1, 0);
	wclrtoeol(hdrwin);

	// TODO: gettext everywhere
	if (span > USECS_PER_SEC * 24 * 60 * 60)
		snprintf(s, sizeof(s), "%s >1 %s (%" PRIu8 ")", "in", "day", exitcode);
	// for the localized decimal point
	else if (span < 1000)
		snprintf(s, sizeof(s), "%s <%.3f%s (%" PRIu8 ")", "in", 0.001, "s", exitcode);
	else snprintf(s, sizeof(s), "%s %.3Lf%s (%" PRIu8 ")", "in", (long double)span/USECS_PER_SEC, "s", exitcode);


#ifdef WITH_WATCH8BIT
	wchar_t *ws;
	skip = mbswidth(s, &ws);
	if (skip == -1)
		return;
	skip = width - skip;
	if (skip >= 0)
		mvwaddwstr(hdrwin, 1, skip, ws);
	free(ws);
#else
	skip = width - (int)strlen(s);
	if (skip >= 0)
		mvwaddstr(hdrwin, 1, skip, s);
#endif
}



// When first_screen, returns false. Otherwise, when WATCH_ALL_DIFF is false,
// return value is unspecified. Otherwise, returns true <==> the character at
// (y, x) changed. After return, cursor position is indeterminate.
//
// The change detection algorithm assumes that all characters (spacing and
// non-spacing) belonging to a set of coords are display_char()d one after
// another. That occurs naturally when writing out text from beginning to end.
//
// The function emulates the behavior ncurses claims to have according to
// curs_add_wch(3x) in that a non-spacing c is added to the spacing character
// already present at (y, x). In reality, ncurses (as of 6.4-20230401) adds it
// to the character at (y, x-1). This affects add_wch() as well as addwstr() et
// al.
static bool display_char(int y, int x, Xint c, int cwid) {
	assert(c != XEOF && c != XL('\0'));  // among other things
	assert(cwid >= 0);
	assert(width-x >= cwid);  // fits
	bool changed = false;
	bool old_standout = false;

#ifdef WITH_WATCH8BIT
// there's an array on stack the size of a function of this
#if (CCHARW_MAX < 3 || CCHARW_MAX > 15)
#error "ncurses' CCHARW_MAX has an unexpected value!"
#endif
	if (! first_screen && flags&WATCH_ALL_DIFF) {
		assert(cwid <= 15);
		static wchar_t oldcc[15][CCHARW_MAX];
		static uf8 oldcclen[15];  // each in [1, CCHARW_MAX)
		static uf8 oldccwid;
		static bool oldstnd;
		static int curx = -1, cury = -1;
		uf8 i, j;
		// This wouldm't work properly if cmd output had a single character and
		// we weren't manually printing ' 's to empty the rest of screen. But
		// when flags&WATCH_ALL_DIFF we are printing the ' 's.
		if (y != cury || x != curx) {
			cchar_t cc;
			short dummy;
			attr_t attr;
			cury = y; curx = x;
			oldstnd = false;
			// If cwid=0, do anything. It shouldn't happen in a proper string.
			oldccwid = cwid;
			// Check every column the new c will occupy. Takes care of, e.g.,
			// 日a -> a日a (日 highlighted because of change in its 2nd column).
			for (i=0; i<cwid; ++i) {
				// terrible interface, so much copying
				mvwin_wch(mainwin, y, x+i, &cc);  // c fits => ok
				getcchar(&cc, oldcc[i], &attr, &dummy, NULL);
				oldstnd |= attr & A_STANDOUT;
				oldcclen[i] = wcslen(oldcc[i]);
				// if nothing else, there is the ' ' there
				assert(oldcclen[i] > 0);
			}
		}

		// If there's no change, then c must be a component of each of the
		// characters. A component not found yet. Find it and mark as found
		// (L'\0').
		for (i=0; i<oldccwid; ++i) {
			for (j=0; j<oldcclen[i]; ++j) {
				if (oldcc[i][j] == (wchar_t)c) {
					oldcc[i][j] = L'\0';
					break;
				}
			}
			if (j == oldcclen[i]) {
				oldccwid = 0;  // mark as changed for good
				break;
			}
		}
		if (! oldccwid)
			changed = true;
		else {
			changed = false;
			for (i=0; i<oldccwid; ++i) {
				for (j=0; j<oldcclen[i]; ++j) {
					if (oldcc[i][j]) {
						changed = true;
						break;
					}
				}
				if (j < oldcclen[i])
					break;
			}
		}

		old_standout = oldstnd;
	}

        if (!(flags & WATCH_FOLLOW))
	        wmove(mainwin, y, x);
	if (cwid > 0) {
		wchar_t c2 = c;
		waddnwstr(mainwin, &c2, 1);
	}
	else {
		cchar_t cc;
		wchar_t wcs[CCHARW_MAX];
		short dummy;
		attr_t dummy2;
		win_wch(mainwin,&cc);
		getcchar(&cc, wcs, &dummy2, &dummy, NULL);
		uf8 len = wcslen(wcs);
		if (len < CCHARW_MAX - 1) {
			wcs[len] = c;
			wcs[len+1] = L'\0';
		}
		setcchar(&cc, wcs, dummy2, dummy, NULL);
		wadd_wch(mainwin, &cc);
	}
#else
	if (! first_screen && flags&WATCH_ALL_DIFF) {
		chtype oldc = mvwinch(mainwin, y, x);
		changed = (unsigned char)c != (oldc & A_CHARTEXT);
		old_standout = oldc & A_STANDOUT;
	}

	wmove(mainwin,y, x);
	waddch(mainwin, c);
#endif

	if (flags & WATCH_DIFF) {
		attr_t newattr;
		short newcolor;
		wattr_get(mainwin, &newattr, &newcolor, NULL);
		// standout can flip on/off as the components of a compound char arrive

		if (changed || (flags&WATCH_CUMUL && old_standout))
			mvwchgat(mainwin, y, x, 1, newattr | A_STANDOUT, newcolor, NULL);
		else
			mvwchgat(mainwin, y, x, 1, newattr & ~(attr_t)A_STANDOUT, newcolor, NULL);
	}

	return changed;
}



static void skiptoeol(FILE *f)
{
	Xint c;
	do c = Xgetc(f);
	while (c != XEOF && c != XL('\n'));
}

static void skiptoeof(FILE *f) {
	unsigned char dummy[4096];
	while (! feof(f) && ! ferror(f))
		(void)!fread(dummy, sizeof(dummy), 1, f);
}

static bool my_clrtoeol(int y, int x)
{
	if (flags & WATCH_ALL_DIFF) {
		bool changed = false;
		while (x < width)
			changed = display_char(y, x++, XL(' '), 1) || changed;
		return changed;
	}

	// make sure color is preserved
	wmove(mainwin, y, x);
	wclrtoeol(mainwin);  // faster, presumably
	return false;
}

static bool my_clrtobot(int y, int x)
{
	if (flags & WATCH_ALL_DIFF) {
		bool changed = false;
		while (y < MAIN_HEIGHT) {
			while (x < width)
				changed = display_char(y, x++, XL(' '), 1) || changed;
			x = 0;
			++y;
		}
		return changed;
	}
	// make sure color is preserved
        if (!(flags & WATCH_FOLLOW)) {
            wmove(mainwin, y, x);
            wclrtobot(mainwin);  // faster, presumably
        }
	return false;
}



// Sets screen_changed: when first_screen, screen_changed=false. Otherwise, when
// ! WATCH_ALL_DIFF, screen_changed will be unspecified. Otherwise,
// screen_changed=true <==> the screen changed.
//
// Make sure not to leak system resources (incl. fds, processes). Suggesting
// -D_XOPEN_SOURCE=600 and an EINTR loop around every fclose() as well.
static uint8_t run_command(void)
{
	int pipefd[2], status;  // [0] = output, [1] = input
	int outfd;
	pid_t child;
	// child will share buffered data, will print it at fclose()
	fflush(stdout);
	fflush(stderr);

	if (use_pty) {
		struct winsize ws;
		memset(&ws, 0, sizeof(ws));
		ws.ws_row = MAIN_HEIGHT;
		ws.ws_col = width;
		child = forkpty(&outfd, NULL, NULL, &ws);
		if (child < 0)
			err(2, _("unable to fork process"));
	} else {
		if (pipe(pipefd) < 0)
			err(2, _("unable to create IPC pipes"));
		child = fork();
		if (child < 0)
			err(2, _("unable to fork process"));
		outfd = pipefd[0];
	}

	if (child == 0) {  /* in child */
		// stdout/err can't be used here. Avoid xerr(), close_stdout(), ...
		// fclose() so as not to confuse _Exit().
		if (!use_pty) {
			fclose(stdout);
			fclose(stderr);
			// connect out and err up with pipe input
			while (close(pipefd[0]) == -1 && errno == EINTR) ;
			while (dup2(pipefd[1], STDOUT_FILENO) == -1 && errno == EINTR) ;
			while (close(pipefd[1]) == -1 && errno == EINTR) ;
			while (dup2(STDOUT_FILENO, STDERR_FILENO) == -1 && errno == EINTR) ;
			// TODO: 0 left open. Is that intentional? I suppose the application
			// might conclude it's run interactively (see ps). And hang if it should
			// wait for input (watch 'read A; echo $A').
		}

		if (flags & WATCH_EXEC) {
			execvp(command_argv[0], command_argv);
			const char *const errmsg = strerror(errno);
			(void)!write(STDERR_FILENO, command_argv[0], strlen(command_argv[0]));
			// TODO: gettext?
			(void)!write(STDERR_FILENO, ": ", 2);
			(void)!write(STDERR_FILENO, errmsg, strlen(errmsg));
			_Exit(0x7f);  // sort of like sh
		}
		status = system(command);
		// errno from system() not guaranteed
		// -1 = error from system() (exec(), wait(), ...), not command
		if (status == -1) {
			(void)!write(STDERR_FILENO, command, command_len);
			// TODO: gettext
			(void)!write(STDERR_FILENO, ": unable to run", 15);
			_Exit(0x7f);
		}
		/* propagate command exit status as child exit status */
		// error msg on stderr provided by sh
		if (WIFEXITED(status))
			_Exit(WEXITSTATUS(status));
		// Else terminated by signal. system() ignores the stopping of children.
		assert(WIFSIGNALED(status));
		_Exit(0x80 + (WTERMSIG(status) & 0x7f));
	}
	/* otherwise, we're in parent */

	if (!use_pty)
		while (close(pipefd[1]) == -1 && errno == EINTR) ;
	FILE *p = fdopen(outfd, "r");
	if (! p)
		endwin_xerr(2, _("fdopen"));
	setvbuf(p, NULL, _IOFBF, BUFSIZ);  // We'll getc() from it. A lot.

	Xint c, carry = XEOF;
	int cwid, y, x;  // cwid = character width in terminal columns
	screen_changed = false;

	for (y = 0; y < MAIN_HEIGHT || (flags & WATCH_FOLLOW); ++y) {
		x = 0;
		while (true) {
			// x is where the next char will be put. When x==width only
			// characters with wcwidth()==0 are output. Used, e.g., for
			// codepoints which modify the preceding character and swallowing a
			// newline / a color sequence / ... after a printable character in
			// the rightmost column.
			assert(x <= width);
			assert(x == 0 || carry == XEOF);

			if (carry != XEOF) {
				c = carry;
				carry = XEOF;
			}
			else c = Xgetc(p);
			assert(carry == XEOF);

			if (c == XEOF) {
                                if (!(flags & WATCH_FOLLOW)) {
				    screen_changed = my_clrtobot(y, x) || screen_changed;
				    y = MAIN_HEIGHT - 1;
                                }
				break;
			}
			if (c == XL('\n')) {
                                if (flags & WATCH_FOLLOW)
                                    waddch(mainwin, c);
                                else
				    screen_changed = my_clrtoeol(y, x) || screen_changed;
				break;
			}
			if (c == XL('\033')) {
				process_ansi(p);
				continue;
			}
			if (c == XL('\a')) {
				beep();
				continue;
			}
			if (c == XL('\t'))  // not is(w)print()
				// one space is enough to consider a \t printed, if there're no
				// more columns
				cwid = 1;
			else {
#ifdef WITH_WATCH8BIT
				// There used to be (! iswprint(c) && c < 128) because of Debian
				// #240989. Presumably because glibc of the time didn't
				// recognize ä, ö, ü, Π, ά, λ, ς, ... as printable. Today,
				// iswprint() in glibc works as expected and the "c<128" is
				// letting all non-printables >=128 get through.
				if (! iswprint(c))
					continue;
				cwid = wcwidth(c);
				assert(cwid >= 0 && cwid <= 2);
#else
				if (! isprint(c))
					continue;
				cwid = 1;
#endif
			}

			// now c is something printable
			// if it doesn't fit
			if (cwid > width-x) {
				assert(cwid > 0 && cwid <= 2);
				assert(width-x <= 1);  // !!
				if (! (flags & WATCH_NOWRAP))
					carry = c;
				else {
					skiptoeol(p);
					reset_ansi();
					set_ansi_attribute(-1, NULL);
				}
				screen_changed = my_clrtoeol(y, x) || screen_changed;
				break;
			}

			// it fits, print it
			if (c == XL('\t')) {
				do screen_changed = display_char(y, x++, XL(' '), 1) || screen_changed;
				while (x % TAB_WIDTH && x < width);
			}
			else {
				// cwid=0 => non-spacing char modifying the preceding spacing
				// char
				screen_changed = display_char(y, x-!cwid, c, cwid) || screen_changed;
				x += cwid;
			}
		}
                if (c == XEOF) {
                    break;
                }
	}

	skiptoeof(p);  // avoid SIGPIPE in child
	fclose(p);

	/* harvest child process and get status, propagated from command */
	// TODO: gettext string no longer used
	while (waitpid(child, &status, 0) == -1) {
		if (errno != EINTR)
			return 0x7f;
	}
	if (WIFEXITED(status))
		return WEXITSTATUS(status);
	assert(WIFSIGNALED(status));
	return 0x80 + (WTERMSIG(status) & 0x7f);
}

static uint8_t run_command_ansi(char ***out_lines, int max_lines, int *out_count)
{
	int pipefd[2], status;
	int outfd;
	pid_t child;
	fflush(stdout);
	fflush(stderr);

	if (use_pty) {
		struct winsize ws;
		memset(&ws, 0, sizeof(ws));
		ws.ws_row = MAIN_HEIGHT;
		ws.ws_col = width;
		child = forkpty(&outfd, NULL, NULL, &ws);
		if (child < 0)
			err(2, _("unable to fork process"));
	} else {
		if (pipe(pipefd) < 0)
			err(2, _("unable to create IPC pipes"));
		child = fork();
		if (child < 0)
			err(2, _("unable to fork process"));
		outfd = pipefd[0];
	}

	if (child == 0) {
		if (!use_pty) {
			fclose(stdout);
			fclose(stderr);
			while (close(pipefd[0]) == -1 && errno == EINTR) ;
			while (dup2(pipefd[1], STDOUT_FILENO) == -1 && errno == EINTR) ;
			while (close(pipefd[1]) == -1 && errno == EINTR) ;
			while (dup2(STDOUT_FILENO, STDERR_FILENO) == -1 && errno == EINTR) ;
		}

		if (flags & WATCH_EXEC) {
			execvp(command_argv[0], command_argv);
			const char *const errmsg = strerror(errno);
			(void)!write(STDERR_FILENO, command_argv[0], strlen(command_argv[0]));
			(void)!write(STDERR_FILENO, ": ", 2);
			(void)!write(STDERR_FILENO, errmsg, strlen(errmsg));
			_Exit(0x7f);
		}
		status = system(command);
		if (status == -1) {
			(void)!write(STDERR_FILENO, command, command_len);
			(void)!write(STDERR_FILENO, ": unable to run", 15);
			_Exit(0x7f);
		}
		if (WIFEXITED(status))
			_Exit(WEXITSTATUS(status));
		assert(WIFSIGNALED(status));
		_Exit(0x80 + (WTERMSIG(status) & 0x7f));
	}

	if (!use_pty)
		while (close(pipefd[1]) == -1 && errno == EINTR) ;
	FILE *p = fdopen(outfd, "r");
	if (!p)
		err(2, _("fdopen"));
	setvbuf(p, NULL, _IOFBF, BUFSIZ);
	*out_lines = ansi_read_lines(p, max_lines, out_count);
	fclose(p);

	while (waitpid(child, &status, 0) == -1) {
		if (errno != EINTR)
			return 0x7f;
	}
	if (WIFEXITED(status))
		return WEXITSTATUS(status);
	assert(WIFSIGNALED(status));
	return 0x80 + (WTERMSIG(status) & 0x7f);
}

int main(int argc, char *argv[])
{
	int i;
	watch_usec_t interval, last_tick = 0, t;
	long max_cycles = 1, cycle_count = 1;
	fd_set select_stdin;
	uint8_t cmdexit;
	struct timeval tosleep;
	bool sleep_dontsleep, sleep_scrdumped, sleep_exit;
	WINDOW *hdrwin = NULL;
	const struct option longopts[] = {
		{"color", no_argument, 0, 'c'},
		{"no-color", no_argument, 0, 'C'},
		{"differences", optional_argument, 0, 'd'},
		{"help", no_argument, 0, 'h'},
		{"interval", required_argument, 0, 'n'},
		{"beep", no_argument, 0, 'b'},
		{"errexit", no_argument, 0, 'e'},
		{"follow", no_argument, 0, 'f'},
		{"chgexit", no_argument, 0, 'g'},
		{"equexit", required_argument, 0, 'q'},
		{"exec", no_argument, 0, 'x'},
		{"precise", no_argument, 0, 'p'},
		{"no-rerun", no_argument, 0, 'r'},
		{"shotsdir", required_argument, 0, 's'},
		{"no-title", no_argument, 0, 't'},
		{"no-wrap", no_argument, 0, 'w'},
		{"version", no_argument, 0, 'v'},
		{0}
	};

	atexit(close_stdout);
	setbuf(stdin, NULL);  // for select()
#ifdef HAVE_PROGRAM_INVOCATION_NAME
	program_invocation_name = program_invocation_short_name;
#endif
	// TODO: when !WATCH8BIT, setlocale() should be omitted or initd as "C",
	// shouldn't it? Also, everywhere we rely on the fact that with !8BIT
	// strlen(s) is the col width of s, for instance.
	// Also, the build system doesn't honor WATCH8BIT when linking. On my system
	// it links against libncursesw even when !WATCH8BIT. That results in half
	// of the program working in wchars, half in chars. On the other hand,
	// people with libncursesw.so probably configure with WATCH8BIT.
	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

#ifdef WITH_COLORWATCH
	flags |= WATCH_COLOR;
#endif /* WITH_COLORWATCH */

	const char *const interval_string = getenv("WATCH_INTERVAL");
	if (interval_string != NULL)
		interval_real = strtod_nol_or_err(interval_string, _("Could not parse interval from WATCH_INTERVAL"));

	while ((i = getopt_long(argc,argv,"+bCcefd::ghq:n:prs:twvx",longopts,NULL)) != EOF) {
		switch (i) {
		case 'b':
			flags |= WATCH_BEEP;
			break;
		case 'c':
			flags |= WATCH_COLOR;
			color_option_seen = true;
			color_explicit = true;
			break;
		case 'C':
			flags &= ~WATCH_COLOR;
			color_option_seen = true;
			color_explicit = false;
			break;
		case 'd':
			flags |= WATCH_DIFF;
			if (optarg)
				flags |= WATCH_CUMUL;
			break;
		case 'e':
			flags |= WATCH_ERREXIT;
			break;
                case 'f':
                        flags |= WATCH_FOLLOW;
                        break;
		case 'g':
			flags |= WATCH_CHGEXIT;
			break;
		case 'q':
			max_cycles = strtol_or_err(optarg, _("failed to parse argument"));
			if (max_cycles < 1)
				max_cycles = 1;
			flags |= WATCH_EQUEXIT;
			break;
		case 'r':
			flags |= WATCH_NORERUN;
			break;
		case 's':
			shotsdir = optarg;
			break;
		case 't':
			flags |= WATCH_NOTITLE;
			break;
		case 'w':
			flags |= WATCH_NOWRAP;
			break;
		case 'x':
			flags |= WATCH_EXEC;
			break;
		case 'n':
			interval_real = strtod_nol_or_err(optarg, _("failed to parse argument"));
			break;
		case 'p':
			flags |= WATCH_PRECISE;
			break;
		case 'h':
			usage(stdout);
			break;
		case 'v':
			printf(PROCPS_NG_VERSION);
			return EXIT_SUCCESS;
		default:
			usage(stderr);
			break;
		}
	}

	if (optind >= argc)
		usage(stderr);

        if ((flags & WATCH_FOLLOW) && (flags & WATCH_ALL_DIFF)) {
            fprintf(stderr, _("Follow -f option conflicts with change options -d,-e or -q"));
            usage(stderr);
        }
	use_ansi = color_option_seen && color_explicit && (flags & WATCH_COLOR);
	use_pty = (flags & WATCH_COLOR);
	if (use_ansi) {
		load_default_fg_from_env();
		load_watch_prefs();
		const char *fade_env = getenv("WATCH_FADE");
		if (fade_env && *fade_env) {
			double v = strtod(fade_env, NULL);
			if (v > 0.0 && v < 1000.0)
				ansi_fade_seconds = v;
		}
		const char *half_env = getenv("WATCH_HALF_LIFE");
		if (half_env && *half_env) {
			if (strcmp(half_env, "1") == 0 || strcasecmp(half_env, "true") == 0)
				ansi_fade_half_life = true;
		}
		const char *fps_env = getenv("WATCH_FPS");
		if (fps_env && *fps_env) {
			long v = strtol(fps_env, NULL, 10);
			if (v > 0 && v <= 60)
				ansi_fade_fps = (int)v;
		}
		const char *max_env = getenv("WATCH_FADE_MAX");
		if (max_env && *max_env) {
			long v = strtol(max_env, NULL, 10);
			if (v < 0)
				v = 0;
			if (v > 255)
				v = 255;
			ansi_fade_max_brightness = (int)v;
		}
		const char *fade_in_env = getenv("WATCH_FADE_IN");
		if (fade_in_env && *fade_in_env) {
			double v = strtod(fade_in_env, NULL);
			if (v > 0.0 && v < 1000.0)
				ansi_fade_in_seconds = v;
		}
		const char *bg_env = getenv("WATCH_FADE_BG");
		if (bg_env && *bg_env) {
			(void)parse_rgb_env(bg_env, &ansi_fade_bg_r, &ansi_fade_bg_g, &ansi_fade_bg_b);
		}
		log_watch_settings();
		if (ansi_fade_in_seconds > 0.0) {
			ansi_fade_in_frames = (int)(ansi_fade_in_seconds * ansi_fade_fps + 0.5);
			if (ansi_fade_in_frames < 1)
				ansi_fade_in_frames = 1;
		}
		if (ansi_fade_seconds > 0.0) {
			if (ansi_fade_half_life) {
				ansi_fade_half_life_frames = (int)(ansi_fade_seconds * ansi_fade_fps + 0.5);
				if (ansi_fade_half_life_frames < 1)
					ansi_fade_half_life_frames = 1;
				ansi_fade_cycles = ansi_fade_half_life_frames * 6;
			} else {
				ansi_fade_cycles = (int)(ansi_fade_seconds * ansi_fade_fps + 0.5);
			}
		}
	}
	command_argv = argv + optind;  // for exec*()
	command_len = strlen(argv[optind]);
	command = xmalloc(command_len+1);  // never freed
	memcpy(command, argv[optind++], command_len+1);
	for (; optind < argc; optind++) {
		size_t s = strlen(argv[optind]);
		/* space and \0 */
		command = xrealloc(command, command_len + s + 2);
		command[command_len] = ' ';
		memcpy(command+command_len+1, argv[optind], s);
		/* space then string length */
		command_len += 1 + s;
		command[command_len] = '\0';
	}

	// interval_real must
	// * be >= 0.1 (program design)
	// * fit in time_t (in struct timeval), which may be 32b signed
	// * be <=31 days (limitation of select(), as per POSIX 2001)
	// * fit in watch_usec_t, even when multiplied by USECS_PER_SEC
	if (interval_real < 0.1)
		interval_real = 0.1;
	if (interval_real > 60L * 60 * 24 * 31)
		interval_real = 60L * 60 * 24 * 31;
	interval = (long double)interval_real * USECS_PER_SEC;
	tzset();

	FD_ZERO(&select_stdin);

	// Catch keyboard interrupts so we can put tty back in a sane state.
	signal(SIGINT, die);
	signal(SIGTERM, die);
	signal(SIGHUP, die);
	signal(SIGWINCH, winch_handler);
	if (use_ansi) {
		setup_terminal_raw();
		setvbuf(stdout, NULL, _IONBF, 0);
		query_default_fg();
		query_default_bg();
		ansi_hide_cursor();
		ansi_get_winsize();
		ansi_reset_prev_buffers(MAIN_HEIGHT);
	} else {
		/* Set up tty for curses use.  */
		initscr();  // succeeds or exit()s, may install sig handlers
		getmaxyx(stdscr, height, width);
		if (flags & WATCH_NOTITLE) {
			mainwin = newwin(height, width, 0,0);
		} else {
			mainwin = newwin(height-HEADER_HEIGHT, width, HEADER_HEIGHT,0);
			hdrwin = newwin(HEADER_HEIGHT, width, 0, 0);
		}
		if (flags & WATCH_FOLLOW)
			scrollok(mainwin, TRUE);
		if (flags & WATCH_COLOR) {
			if (has_colors()) {
				start_color();
				use_default_colors();
				init_ansi_colors();
			}
			else flags &= ~WATCH_COLOR;
		}
		nonl();
		noecho();
		cbreak();
		curs_set(0);
	}

	watch_usec_t next_render = 0;
	while (1) {
		if (use_ansi) {
			char **lines = NULL;
			int line_count = 0;
			bool run_now = true;
			screen_changed = false;
			if (screen_size_changed) {
				screen_size_changed = false;
				ansi_get_winsize();
				ansi_reset_prev_buffers(MAIN_HEIGHT);
				first_screen = true;
			}
			if (!first_screen && !screen_size_changed) {
				watch_usec_t elapsed = get_time_usec() - last_tick;
				if (elapsed < interval)
					run_now = false;
			}
			if (run_now) {
				ansi_move(0, 0);
				t = get_time_usec();
				if (flags & WATCH_PRECISE)
					last_tick = t;
				cmdexit = run_command_ansi(&lines, MAIN_HEIGHT, &line_count);
				if (flags & WATCH_PRECISE)
					ansi_output_headers(get_time_usec() - t, cmdexit);
				else {
					last_tick = get_time_usec();
					ansi_output_headers(last_tick - t, cmdexit);
				}

				int start_row = (flags & WATCH_NOTITLE) ? 0 : HEADER_HEIGHT;
				char **temp_plain = xcalloc((size_t)MAIN_HEIGHT, sizeof(*temp_plain));
				int16_t **temp_new_ages = xcalloc((size_t)MAIN_HEIGHT, sizeof(*temp_new_ages));
				size_t *temp_glyph = xcalloc((size_t)MAIN_HEIGHT, sizeof(*temp_glyph));
				bool any_changed = false;
				for (int row = 0; row < MAIN_HEIGHT; row++) {
					const char *line = (row < line_count && lines[row]) ? lines[row] : "";
					char *plain = strip_ansi_sgr(line);
					bool have_prev = (!first_screen && ansi_prev_plain[row]);
					bool changed = !have_prev || strcmp(plain, ansi_prev_plain[row]) != 0;
					if (have_prev && changed)
						any_changed = true;
					if ((flags & WATCH_ALL_DIFF) && have_prev && changed)
						screen_changed = true;

					size_t plen = strlen(plain);
					size_t prev_len = ansi_prev_plain[row] ? strlen(ansi_prev_plain[row]) : 0;
					size_t glyph_count = utf8_count_glyphs(plain);
					temp_glyph[row] = glyph_count;
					temp_plain[row] = plain;
					int16_t *new_ages = xcalloc(glyph_count, sizeof(*new_ages));
					if (flags & WATCH_DIFF) {
						if (!have_prev) {
							for (size_t i = 0; i < glyph_count; i++)
								new_ages[i] = (int16_t)ansi_fade_cycles;
						} else {
							size_t i = 0;
							size_t pi = 0;
							size_t g = 0;
							while (i < plen && g < glyph_count) {
								size_t seq = utf8_seq_len((unsigned char)plain[i]);
								if (seq > 1 && i + seq > plen)
									seq = 1;
								bool ch = false;
								size_t pseq = 0;
								if (!ansi_prev_plain[row] || pi >= prev_len) {
									ch = true;
								} else {
									pseq = utf8_seq_len((unsigned char)ansi_prev_plain[row][pi]);
									if (pseq > 1 && pi + pseq > prev_len)
										pseq = 1;
									if (seq != pseq || memcmp(plain + i, ansi_prev_plain[row] + pi, seq) != 0)
										ch = true;
								}
								if (ch) {
									new_ages[g] = 0;
								} else if (ansi_char_age[row] && g < ansi_char_age_len[row]) {
									int16_t prev_age = ansi_char_age[row][g];
									if (flags & WATCH_CUMUL) {
										new_ages[g] = prev_age <= 0 ? (int16_t)prev_age : (int16_t)ansi_fade_cycles;
									} else {
										if (prev_age < ansi_fade_cycles)
											new_ages[g] = (int16_t)(prev_age + 1);
										else
											new_ages[g] = (int16_t)ansi_fade_cycles;
									}
								} else {
									new_ages[g] = (int16_t)ansi_fade_cycles;
								}
								i += seq;
								if (!ch && pseq > 0)
									pi += pseq;
								else if (pi < prev_len && pseq > 0)
									pi += pseq;
								g++;
							}
						}
					} else {
						for (size_t i = 0; i < glyph_count; i++)
							new_ages[i] = (int16_t)ansi_fade_cycles;
					}
					temp_new_ages[row] = new_ages;
				}

				if (ansi_fade_in_frames > 0 && any_changed && !first_screen) {
					ansi_pending_active = true;
					ansi_pending_frames = ansi_fade_in_frames;
					for (int row = 0; row < MAIN_HEIGHT; row++) {
						free(ansi_pending_lines[row]);
						free(ansi_pending_plain[row]);
						free(ansi_pending_ages[row]);
						ansi_pending_lines[row] = (row < line_count && lines[row]) ? lines[row] : xstrdup("");
						ansi_pending_plain[row] = temp_plain[row];
						ansi_pending_ages[row] = temp_new_ages[row];
						ansi_pending_age_len[row] = temp_glyph[row];
						if (row < line_count)
							lines[row] = NULL;
						size_t prev_glyphs = utf8_count_glyphs(ansi_prev_plain[row] ? ansi_prev_plain[row] : "");
						int16_t *fadein = build_fadein_ages(
							ansi_prev_plain[row] ? ansi_prev_plain[row] : "",
							ansi_pending_plain[row] ? ansi_pending_plain[row] : "",
							prev_glyphs);
						free(ansi_char_age[row]);
						ansi_char_age[row] = fadein;
						ansi_char_age_len[row] = prev_glyphs;
					}
					ansi_render_current(start_row);
				} else {
					for (int row = 0; row < MAIN_HEIGHT; row++) {
						const char *line = (row < line_count && lines[row]) ? lines[row] : "";
						char *out_line = NULL;
						if (flags & WATCH_DIFF)
							out_line = ansi_apply_char_diff(line, temp_new_ages[row], temp_glyph[row], ansi_fade_cycles);
						else
							out_line = xstrdup(line);
						ansi_write_line(start_row + row, out_line);
						free(out_line);

						free(ansi_prev_lines[row]);
						free(ansi_prev_plain[row]);
						free(ansi_char_age[row]);
						ansi_prev_lines[row] = xstrdup(line);
						ansi_prev_plain[row] = temp_plain[row];
						ansi_char_age[row] = temp_new_ages[row];
						ansi_char_age_len[row] = temp_glyph[row];
					}
				}

				free(temp_plain);
				free(temp_new_ages);
				free(temp_glyph);

				next_render = get_time_usec() + (USECS_PER_SEC / (watch_usec_t)ansi_fade_fps);

				for (int i2 = 0; i2 < line_count; i2++)
					free(lines[i2]);
				free(lines);
			}

			if (cmdexit && (flags & WATCH_BEEP))
				(void)!write(STDOUT_FILENO, "\a", 1);
			if (cmdexit && (flags & WATCH_ERREXIT)) {
				ansi_write_line(height - 1, _("command exit with a non-zero status, press a key to exit"));
				getchar();
				ansi_show_cursor();
				restore_terminal();
				exit(cmdexit);
			}
		} else {
			reset_ansi();
			set_ansi_attribute(-1, NULL);
			if (screen_size_changed) {
				screen_size_changed = false;  // "atomic" test-and-set
				endwin();
				refresh();
				getmaxyx(stdscr, height, width);
				resizeterm(height, width);
				wresize(mainwin, MAIN_HEIGHT, width);
				first_screen = true;
			}

			output_lowheader_pre(hdrwin);
			output_header(hdrwin);
			t = get_time_usec();
			if (flags & WATCH_PRECISE)
				last_tick = t;
			cmdexit = run_command();
			if (flags & WATCH_PRECISE)
				output_lowheader(hdrwin, get_time_usec() - t, cmdexit);
			else {
				last_tick = get_time_usec();
				output_lowheader(hdrwin, last_tick - t, cmdexit);
			}
			wrefresh(hdrwin);

			if (cmdexit) {
				if (flags & WATCH_BEEP)
					beep();  // doesn't require refresh()
				if (flags & WATCH_ERREXIT) {
					// TODO: Hard to see when there's cmd output around it. Add
					// spaces or move to lowheader.
					mvwaddstr(mainwin, MAIN_HEIGHT-1, 0, _("command exit with a non-zero status, press a key to exit"));
					i = fcntl(STDIN_FILENO, F_GETFL);
					if (i >= 0 && fcntl(STDIN_FILENO, F_SETFL, i|O_NONBLOCK) >= 0) {
						while (getchar() != EOF) ;
						fcntl(STDIN_FILENO, F_SETFL, i);
					}
					refresh();
					getchar();
					endwin_exit(cmdexit);
				}
			}
		}

		// [BUG] When screen resizes, its contents change, but not
		// necessarily because cmd output's changed. It may have, but that
		// event is lost. Prevents cycle_count from soaring while resizing.
		if (! first_screen) {
			if (flags & WATCH_CHGEXIT && screen_changed)
				break;
			if (flags & WATCH_EQUEXIT) {
				if (screen_changed)
					cycle_count = 1;
				else {
					if (cycle_count == max_cycles)
						break;
					++cycle_count;
				}
			}
		}

		if (!use_ansi)
			wrefresh(mainwin);  // takes some time
		first_screen = false;

		// first process all available input, then respond to
		// screen_size_changed, then sleep
		sleep_dontsleep = sleep_scrdumped = sleep_exit = false;
		do {
			assert(FD_SETSIZE > STDIN_FILENO);
			FD_SET(STDIN_FILENO, &select_stdin);
			sleep_dontsleep |= screen_size_changed && ! (flags & WATCH_NORERUN);
			if (! sleep_dontsleep && (t=get_time_usec()-last_tick) < interval) {
				watch_usec_t remaining = interval - t;
				if (use_ansi && (flags & WATCH_DIFF) && !(flags & WATCH_CUMUL) && ansi_has_active_fade()) {
					watch_usec_t now = get_time_usec();
					if (next_render == 0)
						next_render = now + (USECS_PER_SEC / (watch_usec_t)ansi_fade_fps);
					if (now < next_render) {
						watch_usec_t until_render = next_render - now;
						if (until_render < remaining)
							remaining = until_render;
					} else {
						remaining = 0;
					}
				}
				tosleep.tv_sec = remaining / USECS_PER_SEC;
				tosleep.tv_usec = remaining % USECS_PER_SEC;
			}
			else memset(&tosleep, 0, sizeof(tosleep));
			i = select(STDIN_FILENO+1, &select_stdin, NULL, NULL, &tosleep);
			assert(i != -1 || errno == EINTR);
			if (i > 0) {
				// all keys idempotent
				switch (getchar()) {
				case EOF:
					if (errno != EINTR) {
						if (use_ansi)
							err(1, "getchar()");
						else
							endwin_xerr(1, "getchar()");
					}
					break;
				case 'q':
					sleep_dontsleep = sleep_exit = true;
					if (use_ansi)
						ansi_exit_newline = 1;
					break;
				case ' ':
					sleep_dontsleep = true;
					break;
				case 's':
					if (! sleep_scrdumped && !use_ansi) {
						screenshot();
						sleep_scrdumped = true;
					}
					break;
				}
			}
			if (use_ansi && (flags & WATCH_DIFF) && !(flags & WATCH_CUMUL)) {
				watch_usec_t now = get_time_usec();
				if (ansi_has_active_fade()) {
					if (next_render == 0)
						next_render = now + (USECS_PER_SEC / (watch_usec_t)ansi_fade_fps);
					if (now >= next_render) {
						watch_usec_t frame = USECS_PER_SEC / (watch_usec_t)ansi_fade_fps;
						do {
							for (int row = 0; row < ansi_prev_count; row++) {
								if (!ansi_char_age[row])
									continue;
								for (size_t i2 = 0; i2 < ansi_char_age_len[row]; i2++) {
									if (ansi_char_age[row][i2] < ansi_fade_cycles)
										ansi_char_age[row][i2]++;
								}
							}
							next_render += frame;
						} while (now >= next_render);
						if (ansi_pending_active) {
							ansi_pending_frames--;
							if (ansi_pending_frames <= 0) {
								for (int row = 0; row < ansi_prev_count; row++) {
									free(ansi_prev_lines[row]);
									free(ansi_prev_plain[row]);
									free(ansi_char_age[row]);
									ansi_prev_lines[row] = ansi_pending_lines[row];
									ansi_prev_plain[row] = ansi_pending_plain[row];
									ansi_char_age[row] = ansi_pending_ages[row];
									ansi_char_age_len[row] = ansi_pending_age_len[row];
									ansi_pending_lines[row] = NULL;
									ansi_pending_plain[row] = NULL;
									ansi_pending_ages[row] = NULL;
									ansi_pending_age_len[row] = 0;
								}
								ansi_pending_active = false;
							}
						}
						ansi_render_current((flags & WATCH_NOTITLE) ? 0 : HEADER_HEIGHT);
					}
				} else {
					next_render = 0;
				}
			}
		} while (i);
		if (sleep_exit)
			break;
	}

	if (use_ansi) {
		if (ansi_exit_newline)
			(void)!write(STDOUT_FILENO, "\n", 1);
		ansi_show_cursor();
		restore_terminal();
		exit(EXIT_SUCCESS);
	}
	endwin_exit(EXIT_SUCCESS);
}
