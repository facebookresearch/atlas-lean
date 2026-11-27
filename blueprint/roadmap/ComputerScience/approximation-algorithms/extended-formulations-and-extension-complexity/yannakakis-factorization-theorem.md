# Yannakakis' factorization theorem

For a polytope $P$ with nonempty interior in its affine hull, given by an inequality description and a vertex description with slack matrix $S$, $\mathrm{xc}(P)$ equals the nonnegative rank of $S$ (up to the convention of adding at most one inequality for degenerate cases). In particular $\mathrm{xc}(P)$ is at least the **rectangle covering number** of the support of $S$, the least number of combinatorial rectangles (products $I \times J$ of row and column sets) contained in $\{(i,j) : S_{ij} \ne 0\}$ that cover it.

## Proof sketch

From an extended formulation, Farkas' lemma expresses each valid inequality of $P$ as a nonnegative combination of the formulation's inequalities, and each vertex lifts to a point $(v_j, y_j)$; the slacks of the lifted points give a nonnegative factorization. Conversely a factorization $S = TU$ yields the formulation $Ax + Ty = b$, $y \ge 0$. Each rank-one term of a nonnegative factorization has rectangular support.

## Depends on

- [Extended formulations and extension complexity](extended-formulation.md)
- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- M. Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences 43(3), 1991.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
