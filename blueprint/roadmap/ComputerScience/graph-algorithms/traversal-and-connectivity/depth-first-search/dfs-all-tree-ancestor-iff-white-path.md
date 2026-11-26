# White-path theorem for depth-first search of the whole graph

In the [depth-first search of the whole graph](dfs-all.md) of a directed graph, $u$ is an
ancestor of $v$ in the
depth-first forest if and only if $v$ is reached from $u$ by a path of edges through vertices
discovered no earlier than $u$, that is, new when $u$ is discovered.

## Background

- [White-path theorem](tree-ancestor-iff-white-path.md): the statement for every numbering with
  the depth-first properties.
- [Depth-first search of the whole graph has the depth-first numbering properties](../strongly-connected-components/dfs-all-is-dfsnumbering.md)

## Sources

- J. Erickson, *Algorithms* (1st ed., 2019), Chapter 6, Lemma 6.1, (a) ⇔ (d).
