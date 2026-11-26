# Stopping-time estimate on finitely many levels

For every $f \colon \mathbb{R} \to E$, every $c \in [0, \infty]$ and every pair of levels $a \le b$, the set $W = \{x : A_k f(x) > c \text{ for some } a \le k \le b\}$ satisfies

$$c\,|W| \le \int_W \|f\|.$$

The proof is the stopping-time argument. For $a \le k \le b$ let $S_k$ be the set of points whose first level in $[a, b]$ with average above $c$ is $k$. The sets $S_k$ are disjoint with union $W$. Membership in $S_k$ depends only on the [averages](dyadic-average.md) at levels $\le k$, which by [nesting](dyadic-index-of-le.md) depend only on the level-$k$ interval of the point; so $S_k$ is a union of level-$k$ intervals, on each of which the average exceeds $c$, that is $c |I| \le \int_I \|f\|$. Summing over these disjoint intervals and over $k$ gives the bound. These are the maximal dyadic intervals of the proof of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Proposition 1.5, restricted to the levels $a, \dots, b$, where maximal intervals always exist.

## Informally uses

- [Nesting of dyadic intervals](dyadic-index-of-le.md): shows that each $S_k$ is a union of level-$k$ intervals.

## Background

- [Dyadic average](dyadic-average.md): the quantity compared with $c$ on each interval.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
