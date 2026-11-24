# Weak type (1,1) of the dyadic maximal function

For every function $f \colon \mathbb{R} \to E$ and every $c \in [0, \infty]$,

$$c \,\big|\{M_d f > c\}\big| \le \int_{\mathbb{R}} \|f(y)\| \, dy,$$

that is, $|\{M_d f > c\}| \le \|f\|_1 / c$ for $c > 0$: the [dyadic maximal function](dyadic-maximal-function.md) maps $L^1$ to weak $L^1$ with constant $1$. This is T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Proposition 1.5, with $d = 1$, without the hypothesis $f \in L^1$ (when $\|f\|_1 = \infty$ the bound is trivial).

The $L^p$ bound $\|M_d f\|_p \le \frac{p}{p-1} \|f\|_p$, $1 < p < \infty$, follows from the [localized form](mul-volume-lt-dyadic-maximal-function-le.md) by the layer-cake formula and Hölder's inequality.

## Informally uses

- [Weak type (1,1), localized form](mul-volume-lt-dyadic-maximal-function-le.md): the right-hand side there is at most $\int \|f\|$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
