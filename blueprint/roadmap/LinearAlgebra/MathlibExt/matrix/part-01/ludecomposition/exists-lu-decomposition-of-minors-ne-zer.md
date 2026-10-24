---
article_id: af_f1a66f10e22b0c18801f2f34
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted.exists_lu_decomposition_of_minors_ne_zero
---

# Exists lu decomposition of minors ne zero

LU decomposition without pivoting: a square matrix whose leading principal minors are all
nonzero factors as a unit-diagonal lower-triangular matrix times an upper-triangular matrix.

Proof: Induct on the dimension and extend the factorization of the leading principal block by a
bordered (Schur-complement) step. The statement is the existence half of Wikipedia, "LU
decomposition", section "Existence and uniqueness".

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.LUDecomposition](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / LU decomposition; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lecture 20.
