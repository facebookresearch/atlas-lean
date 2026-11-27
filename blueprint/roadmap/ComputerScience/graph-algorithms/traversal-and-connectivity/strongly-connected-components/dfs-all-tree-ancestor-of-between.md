# Descendants are numbered consecutively in depth-first search

In the [depth-first search of the whole graph](../depth-first-search/dfs-all.md) of a directed graph, with the vertices
numbered by their preorder index, if $a$ is an ancestor of $d$,
every vertex whose number lies between those of $a$ and $d$ is a descendant of $a$. The proof is
an invariant of the search machine: once a vertex discovered after $a$ is not a descendant of
$a$, all descendants of $a$ have already been discovered.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §2 (proof of Theorem 1: "all vertices numbered during execution of `DFS(w)` are
  descendants of `w`").
