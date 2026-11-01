---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.PseudorandomGrassmannWanted.PseudorandomGrassmann.Φ
---

# Φ

Definition 1.8 from the paper: Let `G = (V,E)` be an `n`-vertex, `d`-regular graph.
For a non-empty set of vertices `S ⊆ V` with `|S| ≤ n/2`, its (edge-)expansion is defined
as `Φ(S) = |E(S,S̄)| / (d·|S|)`, where `E(S,S̄)` denotes the set of edges with one endpoint
in S and the other in `S̄ = V\S`.
In Lean, we don't require the conditions `d`-regular and `|S| ≤ n/2` for this definition.
However, we need `S` nonempty to define the degree `d` as the degree of an arbitrary element
of `S`. Note that this only gives the correct definition for regular graphs.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.PseudorandomGrassmannWanted](../../../../../sources/v2/WantedExt.md)
