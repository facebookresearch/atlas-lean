---
article_id: af_17d8df4f3d27f9f16de11704
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsHsuShiueFamily
---

# Is Hsu Shiue Family

Characterization of the Hsu-Shiue family `S(n, k; alpha, beta, r)`:
the parameters `alpha, beta, r` (real or complex, via `RCLike`) are not all
zero; the initial column is `S n 0 = (r | alpha) n`; and the recurrence
`S (n + 1) (k + 1) = S n k + ((k + 1) * beta - n * alpha + r) * S n (k + 1)`
holds, which is the source recurrence stated at indices where `k - 1`
is defined. The triangular-support condition `S n k = 0` for `n < k`
fixes the otherwise unconstrained initial row (source statement
`jis_7e7402faeeffb59e829d97bc`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Falling Factorial](generalized-falling-factorial.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber](../../../../../../../sources/v2/MathlibExt.md)
