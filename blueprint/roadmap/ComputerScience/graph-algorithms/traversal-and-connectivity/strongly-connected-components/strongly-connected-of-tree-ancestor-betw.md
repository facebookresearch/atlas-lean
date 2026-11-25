# Strongly connected components are closed under tree paths

Under the [numbering properties](is-dfsnumbering.md) (only the first is used), if $a$ is an
ancestor of $b$, $b$ an ancestor of $d$, and $a$ and $d$ are strongly connected, then $b$
and $d$ are strongly connected: $b$ reaches $d$ along tree arcs, and $d$ reaches $a$, which
reaches $b$ along tree arcs. So the vertices of a strongly connected component form a subtree of
the depth-first spanning forest.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Corollary 11.
