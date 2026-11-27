# Multi-splay trees

There is an online BST, the *multi-splay tree*, with the same preferred-path structure as tango trees but with each preferred path stored as a splay tree, whose cost on every access sequence $X$ is $O(\mathrm{OPT}(X) \log\log n)$ and which simultaneously has $O(\log n)$ amortized and $O(\log^2 n)$ worst-case cost per access.

## Proof sketch

The number of preferred-child switches while serving $X$ is at most $\mathrm{IB}_P(X) + 2m$, and a splay-based analysis shows that each switch, carried out by a constant number of splays in auxiliary splay trees of $O(\log n)$ keys, has amortized cost $O(\log\log n)$; Wilber's first bound then gives $O(\mathrm{OPT}(X) \log\log n)$. A generalized access lemma, with a splay-style potential over all auxiliary trees and weights compatible with the reference tree, gives the $O(\log n)$ amortized bound, and the worst case is $O(\log^2 n)$ because an access visits $O(\log n)$ splay trees of $O(\log n)$ keys each.

## Depends on

- [Preferred children and preferred paths](preferred-paths.md)
- [Tango trees](tango-tree.md)
- [Splay operation](../splay-tree/splay.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [Preferred-child changes are counted by the interleave bound](preferred-child-changes-equal-interleave.md)
- [Wilber's first lower bound](../wilber-and-funnel-lower-bounds/wilber-first-bound.md)
- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Sources

- Chengwen Chris Wang, Jonathan Derryberry, Daniel Dominic Sleator, "O(log log n)-Competitive Dynamic Binary Search Trees", SODA (2006).
