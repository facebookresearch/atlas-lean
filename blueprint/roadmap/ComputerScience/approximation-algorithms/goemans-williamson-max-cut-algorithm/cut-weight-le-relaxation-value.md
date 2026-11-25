# The vector relaxation bounds every cut

For $m \ge 1$ and every vertex set $S$, $w(S, \bar S) \le Z_P$: the optimal value of the vector
relaxation (P) in $\mathbb{R}^m$ is an upper bound on the maximum cut. No sign condition on the
weights is needed. Goemans and Williamson state it as $Z^*_P \ge Z^*_{MC}$, which is the same
statement since there are finitely many cuts.

## Informally uses

- [Cuts embed in the vector relaxation](vector-objective-cut-sign-single.md): every cut is the
  objective of (P) at a feasible family of unit vectors.

## Background

- [Weak Lagrange duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md):
  the dual semidefinite program $\frac14 \min\{\sum_j d_j : \operatorname{Diag}(d) \succeq L(G)\}$
  bounds $Z_P$ from above in the same way (Goemans, *Math. Programming* 79 (1997), §5).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, p. 1120.
