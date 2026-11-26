# Word-size-dependent branching factor for fusion trees

Choose the branching factor $B$ as the largest power of two with $16 B^5 \le w$ when $w > 512$, and $B = 2$ otherwise. Then $B \ge 2$, for every $w \ge 5$ the packed sketches and the comparison products of a node with $B$ keys fit in one $w$-bit word, and the multiway predecessor tree built with branching $B$ on $n \ge 1$ keys has height at most $14(1 + \log_w n)$, with the same constant for every word size.

## Proof sketch

For $w > 512$ we have $B \ge (w/16)^{1/5}/2$, so $\log_2 B \ge \frac{1}{5}\log_2 w - c$, and the tree height $\lceil \log_B n \rceil$ is at most a constant times $\log_w n$; for $w \le 512$, $\log_2 n \le 9 \log_w n$. The fitting conditions follow from the sketch length $O(B^4)$ bits per key and $B$ keys per node.

## Depends on

- [Static multiway predecessor tree with cached minima](multiway-predecessor-tree.md)
- [Fusion node](fusion-node.md)

## Proof depends on

- [Collision-free multiplication for approximate sketches](collision-free-multiplication.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
