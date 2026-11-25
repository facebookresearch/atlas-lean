# The first vertex of a component is an ancestor of all of it

Under the [numbering properties](is-dfsnumbering.md), if $u$ is the [first vertex of its strongly
connected component](is-first-in-component.md), then every vertex of the component is a
descendant of $u$. Follow a path from $u$ to a vertex $x$ of the component: all its vertices lie
in the component, and an edge from a descendant of $u$ either leads to a descendant or to a vertex
numbered before its tail, hence, by minimality of $u$ and the consecutive numbering of
descendants, again to a descendant of $u$.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Lemma 10 and Corollary 11 (the root of a component).
