---
article_id: af_0d05859a108a7f8f98ec5d4f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vaughan_identity
---

# Vaughan identity

Vaughan's identity, statement id `vaughan-identity-s1`: the von Mangoldt function `Λ`,
characterized by the Dirichlet convolution `Λ = μ * log` (`hLambda`) with `μ`
the Möbius function (Dirichlet inverse of `1`, `hMu`) and `logW` the logarithm,
at `n > V` with parameters `U`, `V ≥ 1` decomposes into the type-I truncated
`μ * log` sum minus the type-II `μ_{≤U} * Λ_{≤V} * 1` double sum plus the
type-II `μ_{>U} * Λ_{>V} * 1` double sum.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Vaughan identity general](vaughan-identity-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.VaughanIdentity](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Vaughan%27s_identity It follows from `vaughan_identity_general`; the hypotheses `hU` and `hV` are unused and keep the source's shape. Proves `Wanted` entry `vaughan_identity`.
