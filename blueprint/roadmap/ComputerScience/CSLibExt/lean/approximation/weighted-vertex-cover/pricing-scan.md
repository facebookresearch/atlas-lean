---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.pricingScan
---

# Pricing Scan

Scan the remaining edges with residual weights `r` and total price `P`: edge `(u, v)` pays
`δ = min (r u) (r v)`, subtracted from `r u` and `r v`. One unit per edge.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.WeightedVertexCover](../../../../../../sources/v2/CSLibExt.md)
