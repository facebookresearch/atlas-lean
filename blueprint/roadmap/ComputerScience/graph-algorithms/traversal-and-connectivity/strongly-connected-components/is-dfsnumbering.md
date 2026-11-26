# Numbering properties of depth-first search

For a directed graph $G$, a list $P$ of tree arcs and a numbering $\mathrm{num}$ of the vertices,
the numbering properties of depth-first search are the four properties that Tarjan's analysis of
strong connectivity uses:

1. every tree arc $p \to c$ is an edge of $G$;
2. if $a$ is an ancestor of $d$, then $\mathrm{num}(a) \le \mathrm{num}(d)$;
3. the descendants of $a$ are numbered consecutively: if $a$ is an ancestor of $d$ and
   $\mathrm{num}(a) \le \mathrm{num}(x) \le \mathrm{num}(d)$, then $a$ is an ancestor of $x$;
4. every edge $(x, y)$ of $G$ leads to a descendant of $x$ or to a vertex with
   $\mathrm{num}(y) < \mathrm{num}(x)$.

The [depth-first search of the whole graph has these properties](dfs-all-is-dfsnumbering.md).

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §2 (all vertices numbered during `DFS(w)` are descendants of `w`), §3 (ancestors have
  smaller numbers) and §4 (classification of the edges of a directed depth-first search).
