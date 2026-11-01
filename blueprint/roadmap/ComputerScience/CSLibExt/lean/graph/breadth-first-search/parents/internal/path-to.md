---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.BFSForest.pathTo?
---

# Path To?

Follow saved parents, returning the endpoint-inclusive source-to-target list.
Malformed tables are totalized by the visited-vertex count. Costs count source comparisons,
parent reads and actual vertex cons operations, not IO printing latency.

## Depends on

- [BFSForest](bfsforest.md)

## Proof depends on

- [BFSResult](../../../breadth-first-search-2/bfsresult.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Internal](../../../../../../../../sources/v2/CSLibExt.md)
