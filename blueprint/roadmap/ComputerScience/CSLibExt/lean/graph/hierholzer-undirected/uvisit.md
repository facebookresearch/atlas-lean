---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.uvisit
---

# Uvisit

Undirected Hierholzer recursion with fuel: from `v`, take the first remaining edge at `v`,
remove it, recurse at its other endpoint, then continue at `v`; emit `v` when no edge is left at
`v`. Returns the emitted vertices prepended to `acc` and the remaining edges.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Other End](other-end.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
