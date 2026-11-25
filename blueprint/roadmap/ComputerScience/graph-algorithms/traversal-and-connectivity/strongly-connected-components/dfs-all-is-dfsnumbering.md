# Depth-first search of the whole graph has the depth-first numbering properties

The [depth-first search of the whole graph](../depth-first-search/dfs-all.md) of a directed graph, with the vertices numbered by
their preorder index, has the four
[numbering properties of depth-first search](is-dfsnumbering.md): its tree arcs are edges,
ancestors are numbered first, descendants are numbered consecutively, and every edge leads to a
descendant or to an earlier vertex.

## Background

- [Tree arcs of depth-first search of the whole graph are edges](dfs-all-parent-edge.md)
- [Ancestors are discovered first in depth-first search of the whole graph](dfs-all-num-le-of-tree-ancestor.md)
- [Descendants are numbered consecutively in depth-first search](dfs-all-tree-ancestor-of-between.md)
- [Edges of a depth-first search go to descendants or to earlier vertices](dfs-all-edge-cases.md)

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §2–4.
