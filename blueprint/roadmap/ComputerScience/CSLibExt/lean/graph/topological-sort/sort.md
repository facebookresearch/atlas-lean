---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TopologicalSort.sort
---

# Sort

Execute deterministic FIFO Kahn sorting. The executable implementation scans each outgoing
adjacency list twice on a successful run (once while computing initial indegrees and once while
updating neighbors of a processed source) and uses hash-indexed active membership and indegree
storage. Initial-ready vertices follow `g.vertices`; vertices released together follow first
adjacency occurrence.

## Depends on

- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)
- [Result](result.md)

## Proof depends on

- [Has Edge](../directed-adjacency-2/part-02/has-edge.md)
- [Indegree Within](indegree-within.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.TopologicalSort](../../../../../../sources/v2/CSLibExt.md)
