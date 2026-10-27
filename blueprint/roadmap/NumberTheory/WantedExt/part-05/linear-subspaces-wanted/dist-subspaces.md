---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LinearSubspacesWanted.LinearSubspaces.distSubspaces
---

# Dist Subspaces

Finally, in general, if `x = xˡ` is `l`-dimensional and `y = yᵏ` is `k`-dimensional, then
`d(xˡ, yᵏ) = max { d(y¹, xˡ) : y¹ ≤ yᵏ }`, if `k ≤ l`, and
`d(xˡ, yᵏ) = max { d(x¹, yᵏ) : x¹ ≤ xˡ }`, if `k ≥ l`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Dist Line Subspace](dist-line-subspace.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.LinearSubspacesWanted](../../../../../sources/v2/WantedExt.md)
