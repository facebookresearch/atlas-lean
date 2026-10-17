---
article_id: af_d8d4fb95eae0562d036818ff
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
---

# Is Edge Bounded Shortest Path Weight

`distance` is a lower bound for every weighted path with at most `r`
edges, and is either infinity or the weight of an attaining such path.
Paths may repeat vertices; no absence-of-negative-cycles hypothesis is needed.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Weighted Path](../floyd-warshall/basic/is-weighted-path.md)
- [Path Weight](../floyd-warshall/basic/path-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend](../../../../../../../sources/v2/CSLibExt.md)
