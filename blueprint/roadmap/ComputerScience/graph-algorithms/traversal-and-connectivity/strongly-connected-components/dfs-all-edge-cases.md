# Edges of a depth-first search go to descendants or to earlier vertices

In the [depth-first search of the whole graph](../depth-first-search/dfs-all.md) of a directed graph $G$, every edge
$(x, y)$ of $G$ leads
to a descendant of $x$ in the depth-first spanning forest or to a vertex discovered before $x$.
In Tarjan's terms, the edges that are not tree arcs run from ancestors to descendants, from
descendants to ancestors (fronds), or between subtrees (cross-links), and a cross-link $(v, w)$
always has $\mathrm{NUMBER}(v) > \mathrm{NUMBER}(w)$.

The proof is an invariant of the search machine: each adjacency entry $(x, y)$ is examined
while $x$ is on the stack, and every vertex discovered while $x$ is on the stack is a descendant
of $x$.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4.
