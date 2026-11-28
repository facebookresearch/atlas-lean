# Pettie's near-linear bound for deque operations on splay trees

Any sequence of $m$ deque operations on a splay tree initially holding $n$ keys costs $O\big((m + n)\,\alpha^*(m + n)\big)$, where $\alpha^*$ is the iterated inverse Ackermann function, the number of applications of the inverse Ackermann function $\alpha$ needed to reach a constant.

## Proof sketch

Pettie encodes the sequence of rotations as a sequence avoiding a fixed forbidden pattern and bounds its length using extremal results on Davenport–Schinzel sequences, obtaining a bound that is linear up to an $\alpha^*$ factor; this is a strengthening of earlier $O((m+n)\alpha(m+n))$ bounds.

## Depends on

- [Deque and traversal conjectures for splay trees](deque-and-traversal-conjectures.md)
- [Inverse Ackermann function of Tarjan and van Leeuwen](../../disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/inverse-ackermann-tv-l.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Seth Pettie, "Splay Trees, Davenport–Schinzel Sequences, and the Deque Conjecture", SODA (2008), arXiv:0707.2160.
