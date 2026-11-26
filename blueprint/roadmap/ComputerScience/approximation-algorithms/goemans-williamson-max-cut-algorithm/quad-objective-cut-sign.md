# The quadratic program computes cut weights

For every vertex set $S$ with sign vector $y$, $\frac{1}{2}\sum_{i<j} w_{ij}(1 - y_i y_j) = w(S, \bar S)$:
a pair contributes $w_{ij}$ when its endpoints lie on opposite sides and $0$ otherwise. So (Q)
is exactly MAX CUT.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, p. 1120.
