---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.AltPath
---

# Alt Path

An alternating path as listed by `pathTo`: it starts at the right vertex `j`, alternates
non-matching edges (the listed pairs) with matching edges (each listed right vertex after the
first is the partner of the previous listed left vertex), and ends at an unmatched left vertex.
It is an augmenting path when `j` is unmatched too (`IsAugmentingPath`).

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
