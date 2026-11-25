# Cuts embed in the vector relaxation

Let $m \ge 1$, let $e_0$ be the first standard basis vector of $\mathbb{R}^m$ and $y$ the sign
vector of a vertex set $S$. The vectors $v_i = y_i e_0$ are unit vectors, and the
[relaxation objective](vector-objective.md) at them equals the [cut weight](cut-weight.md)
$w(S, \bar S)$. In the words of Goemans and Williamson, (P) reduces to (Q) for vectors lying in a
one-dimensional space.

## Informally uses

- [The quadratic program computes cut weights](quad-objective-cut-sign.md): the objective of (P)
  at $y_i e_0$ is the objective of (Q) at $y$, which is the cut weight.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, p. 1120.
