---
article_id: af_2e4c175a0ed46c21b93dfa51
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.rearickLog
---

# Rearick Log

The Rearick logarithm of a real arithmetic function `f` with `0 < f 1`: it is `0` at `0`,
`Real.log (f 1)` at `1`, and `∑ d ∣ n, f d * f⁻¹ (n / d) * Real.log d` at `n > 1`, where `f⁻¹` is
the Dirichlet inverse of `f`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.RearickLogarithm](../../../../../sources/v2/MathlibExt.md)
