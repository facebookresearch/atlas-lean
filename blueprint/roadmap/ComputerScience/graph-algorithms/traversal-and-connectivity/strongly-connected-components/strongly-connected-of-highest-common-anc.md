# The highest-numbered common ancestor lies in the component

Under the [numbering properties](is-dfsnumbering.md), let $v$ and $w$ be strongly connected and let
$u$ be a common ancestor of $v$ and $w$ in the depth-first spanning forest whose number is at
least that of every common ancestor. Then $u$ lies in the strongly connected component of $v$
and $w$.

## Background

- [Common ancestor of strongly connected vertices](exists-common-ancestor-strongly-connecte.md):
  the proof starts from a common ancestor $u_0$ in the component, which is then an ancestor
  of $u$.
- [Strongly connected components are closed under tree paths](strongly-connected-of-tree-ancestor-betw.md):
  in the proof, $u$ lies on the tree path from $u_0$ to $v$.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Lemma 10.
