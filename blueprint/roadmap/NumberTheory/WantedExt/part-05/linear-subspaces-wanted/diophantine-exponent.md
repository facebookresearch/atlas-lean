---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LinearSubspacesWanted.LinearSubspaces.diophantineExponent
---

# Diophantine Exponent

For a subspace `x ≤ ℝᵈ` and `k : ℕ`, define the diophantine exponent of `x`
for approximation by `k`-dimensional rational subspaces by
`βₖ(x) = inf { β > 0 | ∃ c > 0 : ∀ v ∈ Xₖ(ℚ), d(v, x) ≥ c * H(v)^(−β) }.`

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Rational](is-rational.md)
- [Dist Subspaces](dist-subspaces.md)
- [Height](height.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.LinearSubspacesWanted](../../../../../sources/v2/WantedExt.md)
