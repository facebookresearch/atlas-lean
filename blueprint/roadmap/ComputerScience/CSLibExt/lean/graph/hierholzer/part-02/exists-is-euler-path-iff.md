---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.exists_isEulerPath_iff
---

# Exists is Euler Path iff

When every edge starts at a vertex reachable from `s`, an Euler path from `s` to `t` exists
iff the graph is semi-balanced for `s` and `t`.

## Depends on

- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Edge](../../directed-adjacency-2/part-01/edge.md)
- [Reachable](../../directed-adjacency-2/part-01/reachable.md)
- [Is Euler Path](../part-01/is-euler-path.md)
- [Is Semi Balanced](../part-01/is-semi-balanced.md)

## Proof depends on

- [Hierholzer](../part-01/hierholzer.md)
- [Hierholzer is Euler Path](../part-01/hierholzer-is-euler-path.md)
- [Is Semi Balanced of is Euler Path](../part-01/is-semi-balanced-of-is-euler-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Hierholzer](../../../../../../../sources/v2/CSLibExt.md)
