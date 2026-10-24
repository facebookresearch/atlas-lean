---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.mem_layers_length
---

# Mem layers length

An alternating chain of `L` pairs that ends at an unmatched left vertex reaches its first right
vertex within `L` rounds of the layered search: from the unmatched end, each pair advances one
round.

## Depends on

- [Free](../part-01/free.md)
- [Layers](../part-01/layers.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
