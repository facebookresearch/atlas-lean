# Objective of the MAX CUT semidefinite program

For a real matrix $Y$ indexed by the vertices (only the entries $Y_{ij}$ with $i < j$ enter),

$$\frac12 \sum_{i<j} w_{ij} (1 - Y_{ij}),$$

the objective of the semidefinite form of the relaxation. For symmetric weights and a symmetric
$Y$ with unit diagonal, Goemans's survey writes it as $\frac14 L(G) \bullet Y$ with the weighted
Laplacian $L(G)$.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §4.
- M. X. Goemans, "Semidefinite programming in combinatorial optimization", *Math. Programming* 79 (1997), 143–161 (author's PDF), §5, program (11).
