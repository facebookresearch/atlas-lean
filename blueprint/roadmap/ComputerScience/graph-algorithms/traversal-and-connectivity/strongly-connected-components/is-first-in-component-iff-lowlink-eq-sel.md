# Tarjan's lowlink test for component roots

Under the [numbering properties](is-dfsnumbering.md), a vertex $v$ is the [first vertex of its
strongly connected component](is-first-in-component.md), that is, the root of the subtree formed
by the component, if and only if [$\mathrm{LOWLINK}(v) = v$](lowlink-eq-self.md).

If $v$ is not the root, a path from $v$ to the root $u$ must leave the subtree of $v$; its first
edge $(d, w)$ leaving it starts at a descendant $d$ of $v$ and ends at a vertex $w$ of the
component numbered before $v$, so $\mathrm{LOWLINK}(v) \le w < v$. This test is how Tarjan's
algorithm recognises the roots of the components during a single depth-first search, giving
strongly connected components in $O(V + E)$ time (his Theorem 13).

## Informally uses

- [The first vertex of a component is an ancestor of all of it](tree-ancestor-of-first.md): the
  root $u$ of the component of $v$ is a proper ancestor of $v$ when $v$ is not the root
  (Corollary 11).
- [The highest-numbered common ancestor lies in the component](strongly-connected-of-highest-common-anc.md):
  Tarjan's proof uses Lemma 10 to place the endpoint $w$ of the first edge leaving the subtree of
  $v$ in the component.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Lemma 12 (and Theorem 13 for the algorithm).
