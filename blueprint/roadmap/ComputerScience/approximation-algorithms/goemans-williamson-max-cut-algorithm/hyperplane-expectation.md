# Expected weight of the random-hyperplane cut

For vectors $v_i$, the closed form

$$\sum_{i<j} w_{ij} \, \frac{\arccos(v_i \cdot v_j)}{\pi}.$$

By Theorem 3.1 of Goemans and Williamson it is the expected weight of the cut
$\{i : v_i \cdot r \ge 0\}$ for a random direction $r$, when the $v_i$ are unit vectors. The
definition is only the expression; the probabilistic identity is
[Theorem 3.1](integral-cut-weight-hyperplane.md).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Theorem 3.1.
