# Fusion trees answer predecessor queries in O(log_w n) time

For every word size $w \ge 5$ and every set of $n \ge 1$ distinct $w$-bit keys there is a static fusion tree occupying at most $126 n + 18$ words such that one fixed word-RAM program (depending only on $w$, with a code size bound uniform in $w$) answers every inclusive predecessor query in at most $3\,100\,000\,(\lfloor \log_w n \rfloor + 1)$ instructions. In particular predecessor search takes $O(\log n / \log w)$ time in linear space, which beats binary search, $O(\log n)$, whenever $w$ grows with $n$.

The branching factor is chosen as a power of two $B \ge 2$ with $16 B^5 \le w$ for $w > 512$ (and $B = 2$ otherwise), giving tree height at most $14(1 + \log_w n)$ for all widths with one constant.

## Proof sketch

Build the multiway predecessor tree with branching $B = w^{\Theta(1)}$ and turn each internal node into a fusion node on its children's cached minima. A query descends one root-to-leaf path, spending $O(1)$ instructions per node by the constant-time node rank, and the height is $O(\log_B n) = O(\log_w n)$.

## Depends on

- [Fusion node](fusion-node.md)
- [Static multiway predecessor tree with cached minima](multiway-predecessor-tree.md)
- [Static predecessor problem on word keys](static-predecessor-problem.md)

## Proof depends on

- [Constant-time rank in a fusion node](constant-time-rank-in-a-fusion-node.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
