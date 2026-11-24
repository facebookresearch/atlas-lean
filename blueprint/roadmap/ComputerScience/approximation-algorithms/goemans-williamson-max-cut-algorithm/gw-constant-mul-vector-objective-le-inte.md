# Goemans–Williamson Theorem 3.3

For nonnegative weights, unit vectors $v_i \in \mathbb{R}^n$ and a standard Gaussian vector $r$, the
cut $S = \{i : v_i \cdot r \ge 0\}$ satisfies

$$\mathbb{E}[w(S, \bar S)] \ge \alpha \cdot \frac12 \sum_{i<j} w_{ij}(1 - v_i \cdot v_j).$$

## Informally uses

- [Theorem 3.1](integral-cut-weight-hyperplane.md): the expected weight in closed form.
- [Term-by-term comparison](gw-constant-mul-vector-objective-le.md): Lemma 3.4 applied to each
  pair.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Theorem 3.3.
