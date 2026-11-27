# Objective of the MAX CUT quadratic program

For weights $w_{ij}$ and a vector $y \in \mathbb{R}^V$,

$$\frac{1}{2} \sum_{i<j} w_{ij} (1 - y_i y_j),$$

the objective of the integer quadratic program (Q) of Goemans and Williamson, which maximizes it
over $y \in \{-1, 1\}^V$. Here $y$ is any real vector; the $\pm 1$ case is
[the weight of a cut](quad-objective-cut-sign.md).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, program (Q).
