---
article_id: af_8edd198d9d6f70f850a6f0d9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vaughan_identity_general
---

# Vaughan identity general

Vaughan's identity with only the hypotheses the argument uses: for any `U` and any `V < n`,
with `Λ = μ * logW` (`hLambda`) and `μ` the Dirichlet inverse of `1` (`hMu`), `Λ n` is the
truncated `μ * log` sum minus the `μ_{≤U} * Λ_{≤V} * 1` double sum plus the
`μ_{>U} * Λ_{>V} * 1` double sum. `vaughan_identity` is the source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.VaughanIdentity](../../../../../sources/v2/MathlibExt.md)
