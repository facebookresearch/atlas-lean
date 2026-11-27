# Tarjan's lowlink test for depth-first search of the whole graph

In the [depth-first search of the whole graph](../depth-first-search/dfs-all.md) of a directed graph, with the vertices
numbered by their preorder index, a vertex
$v$ is the first vertex of its strongly connected component if and only if
$\mathrm{LOWLINK}(v) = v$.

## Background

- [Tarjan's lowlink test for component roots](is-first-in-component-iff-lowlink-eq-sel.md)
- [Depth-first search of the whole graph has the depth-first numbering properties](dfs-all-is-dfsnumbering.md)

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Lemma 12.
