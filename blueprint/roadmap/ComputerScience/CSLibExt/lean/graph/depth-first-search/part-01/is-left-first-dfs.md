---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DepthFirstSearch.IsLeftFirstDFS
---

# Is Left First DFS

A traversal conforms to left-first DFS when it is the result of the declarative
machine relation that consumes roots from left to right and, on discovery, places
the ordered adjacency list before the vertex's exit and all remaining work.

## Depends on

- [Traversal](traversal.md)
- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)

## Proof depends on

- [Steps](steps.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch](../../../../../../../sources/v2/CSLibExt.md)
