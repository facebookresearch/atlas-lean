---
article_id: af_7b5a8b8f73c36d2e9ba1974a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Matrix.exists_unitaryGroup_diagonal_nonneg
---

# SVD

Singular value decomposition: every square complex matrix is `U * diagonal σ * star V` for some
`U V : Matrix.unitaryGroup n ℂ` and nonnegative `σ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.Factorizations.SVD](../../../../../../sources/v2/MathlibExt.md)
- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013). Proves `Wanted` entry `complex_svd`, restated over `Matrix.unitaryGroup` in place of the entry's `IsUnitaryMatrix`.
