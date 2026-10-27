---
article_id: af_2b43be56b58fda4afe13e8c2
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
---

# Ordinary Riordan Pascal Like Matrix

Ordinary Riordan Pascal-like matrix entry `T(n, k; r)` (concept
`jis_sem_d14a1d74e61f27c561413829`; statements `jis_55826aed9bbc43db2e540fc8`,
`jis_a1500757725c00536c86ba35`, `jis_ac99ac2ae8aedbaafe1c53e3`).

This is the entry formula for the ordinary Riordan array
`(1 / (1 - x), x * (1 + r * x) / (1 - x))`, denoted `T(r)`, with integer
parameter `r`. The second binomial factor is written `choose (n - j) k` by
binomial symmetry, so terms with `j > n - k` vanish rather than being
corrupted by truncated subtraction. Source specializations: `r = 0` gives
Pascal's triangle and `r = 1` gives the Delannoy triangle.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix](../../../../../../sources/v2/MathlibExt.md)
