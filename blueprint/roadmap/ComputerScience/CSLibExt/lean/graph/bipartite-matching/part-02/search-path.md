---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.searchPath
---

# Search Path

`pathTo` restricted to unused vertices, as a depth-first search over the layers with the
pruning of Hopcroft and Karp: from a reached right vertex `j` that is not dead, descend to the
round where `j` is first reached and try each predecessor `i` of the round before that is not in
`usedL`, continuing from the partner of `i`. A right vertex from which the search fails is marked
dead, so each right vertex fails at most once per phase. Returns the path found, if any, and the
dead set.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Layers](../part-01/layers.md)
- [Partner Of](partner-of.md)
- [Try Preds](try-preds.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
