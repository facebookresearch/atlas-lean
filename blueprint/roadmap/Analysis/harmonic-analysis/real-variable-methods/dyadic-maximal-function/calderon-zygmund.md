# Calderón–Zygmund decomposition, dyadic form

Let $f \colon \mathbb{R} \to E$ with $\|f\|$ a.e. measurable and $\int \|f\| < \infty$, let $c \ne 0$, and let $\Omega = \{M_d f > c\}$. Then:

1. $c\,|\Omega| \le \int \|f\|$;
2. $\|f(x)\| \le c$ for almost every $x \notin \Omega$;
3. every $x \in \Omega$ has a [stopping level](is-stopping-level.md) $k$, and the level-$k$ dyadic interval $Q \ni x$ satisfies $c < \frac{1}{|Q|} \int_Q \|f\| \le 2c$, lies in $\Omega$, and is the stopping interval of each of its points.

By item 3, and since two stopping intervals are equal or disjoint, the stopping intervals form a partition $\Omega = \bigsqcup_j Q_j$ into maximal dyadic intervals, with $\sum_j |Q_j| = |\Omega| \le \|f\|_1 / c$. This is the construction in the proof of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Proposition 7.11, in dimension $d = 1$, where $2^d \lambda = 2\lambda$.

Relation to the source: Proposition 7.11 states the decomposition $f = g + b$ with $\|g\|_\infty \le 2^d \lambda$, $\|g\|_1 \le \|f\|_1$ and $b = \sum_Q b_Q$, $\int b_Q = 0$, $\int |b_Q| \le 2 \int_Q |f|$. The statement gives the cubes and the bounds that define $g = f\,\mathbf{1}_{\Omega^c} + \sum_j \langle f \rangle_{Q_j} \mathbf{1}_{Q_j}$ and $b = f - g$, but does not form $g$ and $b$; in that respect it is weaker than the source.

## Informally uses

- [Weak type (1,1) of the dyadic maximal function](dyadic-maximal-function-mul-volume-le-li.md): item 1.
- [Pointwise domination by the dyadic maximal function](ae-enorm-le-dyadic-maximal-function.md): item 2.
- [Existence of the stopping level](exists-is-stopping-level.md): item 3.
- [Stopping level](is-stopping-level.md): the upper bound $2c$ and the constancy of the stopping level on $Q$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
