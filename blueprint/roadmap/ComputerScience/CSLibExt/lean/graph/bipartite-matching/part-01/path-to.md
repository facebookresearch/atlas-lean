---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.pathTo
---

# Path To

Walk the layers back from a reached right vertex `j` (reached by round `k + 1`): go down to
the round where `j` is first reached, take a predecessor `i` of the round before, and, unless `i`
is unmatched, continue from the partner of `i`. The result lists the pairs to match, `j` first.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Layers](layers.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
