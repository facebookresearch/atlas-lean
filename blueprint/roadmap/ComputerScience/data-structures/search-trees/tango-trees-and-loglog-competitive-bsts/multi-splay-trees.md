# Multi-splay trees

There is an online BST, the *multi-splay tree*, with the same preferred-path structure as tango trees but with each preferred path stored as a splay tree, whose cost on every access sequence $X$ of length $m$ is $O((\mathrm{OPT}(X) + n) \log\log n)$, hence $O(\mathrm{OPT}(X) \log\log n)$ whenever $m = \Omega(n)$, and which simultaneously has $O(\log n)$ amortized and $O(\log^2 n)$ worst-case cost per access.

## Proof sketch

The number of preferred-child switches while serving $X$ is at most $\mathrm{IB}_P(X) + 2m$, and a splay-based analysis shows that each switch, carried out by a constant number of splays in auxiliary splay trees of $O(\log n)$ keys, has amortized cost $O(\log\log n)$, with an initial potential of $O(n \log\log n)$ (each key contributes the logarithm of a size at most $O(\log n)$); Wilber's first bound, $\mathrm{OPT}(X) \ge \mathrm{IB}_P(X)/2 - O(n) + m$, then gives $O((\mathrm{OPT}(X) + n) \log\log n)$, and the additive $O(n \log\log n)$ term, like the at most $2n - 2$ rotations separating two initial trees, is absorbed once $m = \Omega(n)$. A generalized access lemma, with a splay-style potential over all auxiliary trees and weights compatible with the reference tree, gives the $O(\log n)$ amortized bound, and the worst case is $O(\log^2 n)$ because an access visits $O(\log n)$ splay trees of $O(\log n)$ keys each.

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
