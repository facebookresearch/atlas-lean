---
article_id: af_debc94df4605a5d541732a44
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Matrix.exists_unitaryGroup_posSemidef
---

# Exists unitary Group pos Semidef

Polar decomposition: every square complex matrix is `U * P` for some
`U : Matrix.unitaryGroup n ℂ` and positive semidefinite `P` with `P * P = Aᴴ * A`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [SVD](../exists-unitary-group-diagonal-nonneg.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.Factorizations.Polar](../../../../../../../sources/v2/MathlibExt.md)
- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013). Proves `Wanted` entry `polar_decomposition`, restated over `Matrix.unitaryGroup` in place of the entry's `IsUnitaryMatrix`.
