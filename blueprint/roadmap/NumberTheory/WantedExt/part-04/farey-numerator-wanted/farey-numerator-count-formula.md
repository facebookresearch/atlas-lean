---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.FareyNumeratorWanted.fareyNumeratorCount_formula
---

# Theorem 1

**Theorem 1**: for `0 < h < n`,
`N_n(h) = φ(h) * (n / h) - ∑_{d ∣ h} μ(d) {n / d}
  - φ(h) + δ_{1h}`, where `μ` is the Möbius function,
`{x}` is the fractional part (written `(n % d) / d`)
and `δ_{1h}` is `1` if
`h = 1` and `0` otherwise.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FareyNumeratorWanted](../../../../../sources/v2/WantedExt.md)
- Rogelio Tomás García, "Farey Fractions with Equal Numerators and the Rank of Unit Fractions", Theorem 1.
