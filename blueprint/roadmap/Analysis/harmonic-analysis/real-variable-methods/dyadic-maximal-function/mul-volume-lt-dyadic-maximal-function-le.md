# Weak type (1,1) of the dyadic maximal function, localized form

For every function $f \colon \mathbb{R} \to E$ and every $c \in [0, \infty]$,

$$c \,\big|\{M_d f > c\}\big| \le \int_{\{M_d f > c\}} \|f(y)\| \, dy,$$

where $M_d$ is the [dyadic maximal function](dyadic-maximal-function.md).

This is the sharper inequality obtained at the end of the proof of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Proposition 1.5 (case $d = 1$). The statement here is stronger than the source in one respect: it holds for every $f$, not only for $f \in L^1$. The source uses $f \in L^1$ to guarantee that maximal dyadic intervals with average above $c$ exist; the proof here instead restricts to the levels $-N \le k \le N$, applies the [finite-level estimate](mul-volume-window-le.md), and lets $N \to \infty$ by continuity of measure along increasing unions. This is the localization in the proof of Proposition 1.9 of the same notes, which truncates to cubes of side length at most $2^n$ for general measures, where the side-length argument of Proposition 1.5 is unavailable.

## Informally uses

- [Stopping-time estimate on finitely many levels](mul-volume-window-le.md): the bound for the levels $-N, \dots, N$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
