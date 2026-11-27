# Fusion trees answer predecessor queries in O(log_w n) time

On the word RAM with multiplication, for every word size $w \ge 2$ and every set of $n \ge 1$ distinct $w$-bit keys there is a static fusion tree occupying $O(n)$ words that answers every inclusive predecessor query in $O(1 + \log_w n)$ time (Demaine, 6.851 Lecture 12, Section 12.2, following Fredman and Willard). In particular predecessor search takes $O(1 + \log n / \log w)$ time in linear space, which beats binary search, $O(\log n)$, whenever $w$ grows with $n$.

The branching factor is the one of [Word-size-dependent branching factor for fusion trees](fusion-tree-branching-factor.md), $B = \Theta(w^{1/5})$ with $B \ge 2$, giving tree height $O(1 + \log_w n)$.

## Proof sketch

Build the multiway predecessor tree with branching $B = w^{\Theta(1)}$ and turn each internal node into a fusion node on its children's cached minima. A query descends one root-to-leaf path, spending $O(1)$ instructions per node by the constant-time node rank, and the height is $O(1 + \log_B n) = O(1 + \log_w n)$.

## Depends on

- [Fusion node](fusion-node.md)
- [Static multiway predecessor tree with cached minima](multiway-predecessor-tree.md)
- [Static predecessor problem on word keys](static-predecessor-problem.md)
- [Word-size-dependent branching factor for fusion trees](fusion-tree-branching-factor.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Constant-time rank in a fusion node](constant-time-rank-in-a-fusion-node.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
