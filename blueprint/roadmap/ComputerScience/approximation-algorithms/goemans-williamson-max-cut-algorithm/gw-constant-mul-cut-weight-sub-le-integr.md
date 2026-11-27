# The Goemans–Williamson guarantee for nearly optimal vectors

Let the weights be nonnegative, $n \ge 1$, $\varepsilon \in \mathbb{R}$, and let unit vectors
$v_i \in \mathbb{R}^n$ have relaxation objective at least $Z_P - \varepsilon$. Then for every vertex set
$S'$ the random-hyperplane cut $S = \{i : v_i \cdot r \ge 0\}$, with $r$ a standard Gaussian vector
in $\mathbb{R}^n$, satisfies

$$\mathbb{E}[w(S, \bar S)] \ge \alpha \left(w(S', \bar{S'}) - \varepsilon\right).$$

Goemans and Williamson state the guarantee in the slightly stronger form
$\alpha(Z_P - \varepsilon)$: for integral weights and $\varepsilon > 0$, a semidefinite-programming
algorithm returns, in time polynomial in the input size and $\log(1/\varepsilon)$, vectors of value greater than
$Z_P - \varepsilon$, and the cut
then has expected weight at least $\alpha(Z_P - \varepsilon) \ge \alpha(\mathrm{OPT} - \varepsilon)$. The
statement above is the consequence for every cut, $\alpha(w(S', \bar{S'}) - \varepsilon)$, which
with $S'$ a maximum cut is $\alpha(\mathrm{OPT} - \varepsilon)$.

## Informally uses

- [The vector relaxation bounds every cut](cut-weight-le-relaxation-value.md) and
  [Theorem 3.3](gw-constant-mul-vector-objective-le-inte.md).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, p. 1121.
