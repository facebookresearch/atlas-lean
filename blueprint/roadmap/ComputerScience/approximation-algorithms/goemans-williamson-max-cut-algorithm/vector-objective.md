# Objective of the vector relaxation

For vectors $v_i \in \mathbb{R}^m$,

$$\frac{1}{2} \sum_{i<j} w_{ij} (1 - v_i \cdot v_j),$$

the objective of the relaxation (P) of Goemans and Williamson, which maximizes it over unit
vectors. With $Y_{ij} = v_i \cdot v_j$ it is a linear function of the positive semidefinite
Gram matrix $Y$ with unit diagonal; this is how (P) becomes a semidefinite program (their §4).

## Background

- [Theta function of a graph](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/README.md):
  the Lovász theta function, defined by vector labelings in the same way, is the other basic
  semidefinite relaxation in combinatorial optimization (Goemans, *Math. Programming* 79 (1997),
  §3 and §5).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, relaxation (P).
