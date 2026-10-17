---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.franel_landau
---

# Franel Landau Theorem Wanted

Franel-Landau theorem (statement_id `franel-landau-s1`, canonical name
"Franel-Landau theorem"): with `F_N = Farey.fareySeq N` and zero-based list
index `k`, let `δ_k = F_N[k] - k / (F_N.length - 1)`. The Riemann hypothesis
holds iff for every
`ε > 0`, `∑_k δ_k ^ 2 = O(N ^ (-1 + ε))` as `N → ∞`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FranelLandauTheoremWanted](../../../../sources/v2/WantedExt.md)
- https://en.wikipedia.org/wiki/Farey_sequence.
