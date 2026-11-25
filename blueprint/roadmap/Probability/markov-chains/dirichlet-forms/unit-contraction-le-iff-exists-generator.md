# Beurling–Deny on $\mathbb{R}^n$: unit-contractive forms come from sub-Markovian generators

Let $S$ be a finite set and $A$ a real symmetric $S \times S$ matrix with [bilinear
form](matrix-form.md) $a(u, v) = \sum_{x, y} u(x) A(x, y) v(y)$. Then
$a(\bar u, \bar u) \le a(u, u)$ for every $u : S \to \mathbb{R}$, where $\bar u = (0 \vee u) \wedge 1$
is the [unit contraction](unit-contraction.md), if and only if there is a real symmetric
$S \times S$ matrix $Q$ with $Q(x, y) \ge 0$ for $x \ne y$ and $\sum_y Q(x, y) \le 0$ for every $x$
such that $a(u, v) = \mathcal E_{1, Q}(u, v)$ for all $u, v$, where $\mathcal E_{1, Q}$ is the
[form](form.md) (1.2.27) with counting measure $m = 1$. One can take $Q = -A$.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Section 1.1 and Example 1.2.5.
