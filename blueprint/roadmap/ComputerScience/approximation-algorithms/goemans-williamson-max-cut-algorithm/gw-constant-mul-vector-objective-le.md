# Goemans–Williamson Theorem 3.3, term-by-term comparison

For nonnegative weights and unit vectors $v_i \in \mathbb{R}^m$,

$$\alpha \cdot \frac12 \sum_{i<j} w_{ij}(1 - v_i \cdot v_j) \le \sum_{i<j} w_{ij} \frac{\arccos(v_i \cdot v_j)}{\pi}.$$

This is the inequality by which Goemans and Williamson prove Theorem 3.3; the right-hand side is
the expected weight of the random-hyperplane cut by their
[Theorem 3.1](integral-cut-weight-hyperplane.md); combined, they give [Theorem 3.3](gw-constant-mul-vector-objective-le-inte.md). Applied to vectors whose
value is within $\varepsilon$ of $Z_P$, it gives a random cut of expected weight at least
$\alpha (Z_P - \varepsilon) \ge \alpha(\mathrm{OPT} - \varepsilon)$. Nonnegativity of the
weights is used: each term is multiplied by $w_{ij}$.

## Informally uses

- [Lemma 3.4](gw-constant-mul-le-arccos-div-pi.md): applied to each pair with
  $y = v_i \cdot v_j \in [-1, 1]$.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Theorem 3.3 and its proof.
