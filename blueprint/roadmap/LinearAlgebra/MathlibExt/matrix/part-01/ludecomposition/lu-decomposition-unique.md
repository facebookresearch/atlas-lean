---
article_id: af_a59cfb9548f157b675719282
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted.lu_decomposition_unique
---

# Lu decomposition unique

Uniqueness of the LU decomposition with unit diagonal for an invertible matrix.

Proof: Move the invertible triangular factors across the equality, then use the triangular inverse
and diagonal formulas to show the resulting matrix is the identity. The statement is the
uniqueness half of Wikipedia, "LU decomposition", section "Existence and uniqueness".

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.LUDecomposition](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear inequalities / LU decomposition; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997), Lecture 20.
