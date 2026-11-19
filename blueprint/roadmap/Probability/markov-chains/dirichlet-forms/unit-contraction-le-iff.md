# Beurling–Deny criterion on $\mathbb{R}^n$

Let $S$ be a finite set and $A$ a real symmetric $S \times S$ matrix with [bilinear
form](matrix-form.md) $a(u, v) = \sum_{x, y} u(x) A(x, y) v(y)$. The unit contraction operates on
$a$, that is $a(\bar u, \bar u) \le a(u, u)$ for every $u : S \to \mathbb{R}$ with
$\bar u = (0 \vee u) \wedge 1$ the [unit contraction](unit-contraction.md), if and only if
$A(x, y) \le 0$ for all $x \ne y$ and $\sum_y A(x, y) \ge 0$ for every $x$. This is the
finite-dimensional case of the Markov property (E.4)′ of Fukushima, Oshima and Takeda: sufficiency
is their Example 1.2.5 with $m = 1$ and $Q = -A$; necessity is tested on $u = \mathbf 1_x - c\, \mathbf 1_y$
and $u = 1 + c\, \mathbf 1_x$ for small $c > 0$.

Here $\mathbb R^n = \mathbb R^S$ carries counting measure, and every form on it is closed, so the
criterion characterises the Dirichlet forms on $\ell^2(S)$. For weights $m > 0$ the same holds with
$-A$ replaced by the generator $Q = -\operatorname{diag}(m)^{-1} A$, which is in detailed balance with
$m$.

## Background

- [Laplacian Rayleigh quotient of a spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/laplacian-rayleigh-quotient.md): graph Laplacians $D - A$ are the
  conservative examples (zero row sums).
- [Rate matrices](../finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md): $-A$ is a symmetric rate matrix exactly when the row sums of $A$ vanish.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Section 1.1, condition (E.4)′, and Example 1.2.5.
