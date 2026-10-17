---
article_id: af_1c383cc28810cc9e26981306
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Matrix.exists_unitaryGroup_isUpperTriangular
---

# Schur

Schur decomposition: every square complex matrix is `U * T * star U` for some
`U : Matrix.unitaryGroup n ℂ` and upper-triangular `T`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.Factorizations.Schur](../../../../../../sources/v2/MathlibExt.md)
- I. Schur, Uber charakteristische Wurzeln, Math. Ann. 66 (1909), 488-510, DOI 10.1007/BF01450045. Proves `Wanted` entry `schur_decomposition`, restated over `Matrix.unitaryGroup` in place of the entry's `IsUnitaryMatrix`.
