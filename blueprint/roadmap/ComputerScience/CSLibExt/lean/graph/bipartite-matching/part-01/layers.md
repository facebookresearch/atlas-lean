---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.layers
---

# Layers

The alternating breadth-first layers, cumulative on both sides: `(layers adj mate k).1` are the
left vertices reached within `k` rounds (initially the unmatched ones), and `(layers adj mate k).2`
the right vertices reached within `k` rounds (through a non-matching edge from a left vertex
reached within `k - 1` rounds). The round where a vertex is first reached is its breadth-first
level; `pathTo` descends to it.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Free](free.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
