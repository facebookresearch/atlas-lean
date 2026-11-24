# The Goemans–Williamson guarantee

Let the weights be nonnegative, $n \ge 1$, and let unit vectors $v_i \in \mathbb{R}^n$ attain the
relaxation value $Z_P$ in $\mathbb{R}^n$. Then for every vertex set $S'$, the random-hyperplane cut
$S = \{i : v_i \cdot r \ge 0\}$, with $r$ a standard Gaussian vector in $\mathbb{R}^n$, satisfies

$$\mathbb{E}[w(S, \bar S)] \ge \alpha \cdot w(S', \bar{S'}),$$

so its expected weight is at least $\alpha > 0.87856$ times the maximum cut. The statement assumes
that the vectors attain the supremum; Goemans and Williamson work with vectors of value at least
$Z_P - \varepsilon$, which is the [version for nearly optimal vectors](gw-constant-mul-cut-weight-sub-le-integr.md).

## Informally uses

- [The vector relaxation bounds every cut](cut-weight-le-relaxation-value.md) and
  [Theorem 3.3](gw-constant-mul-vector-objective-le-inte.md).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2 and Theorem 3.3.
