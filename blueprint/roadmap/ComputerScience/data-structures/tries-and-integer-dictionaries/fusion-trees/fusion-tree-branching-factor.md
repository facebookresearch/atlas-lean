# Word-size-dependent branching factor for fusion trees

Choose the branching factor as $B = \Theta(w^{1/5})$ with $B \ge 2$; any fixed small positive power of $w$ would do. Then the approximate sketches of the at most $B$ keys of a fusion node, each spanning $O(B^4)$ bit positions, occupy $O(B^5) = O(w)$ bits in total, a constant number of words, and the multiway predecessor tree built with branching $B$ on $n \ge 1$ keys has height $O(1 + \log_w n)$, the $\Theta(\log_w n)$ height of the fusion tree (Demaine, 6.851 Lecture 12, Sections 12.3 and 12.6).

## Proof sketch

With $B \ge c\, w^{1/5}$ for a constant $c > 0$, the height $\lceil \log_B n \rceil$ is at most a constant times $\log_w n$, plus one. The sketch length $O(B^4)$ per key and $B$ keys per node give the fitting bound. An explicit choice: let $B$ be the largest power of two with $16 B^5 \le w$ when $w > 512$, and $B = 2$ otherwise. Then the height is at most $14 \log_w n + 1 \le 14(1 + \log_w n)$ for every $w \ge 2$. For $w \le 512$, $\lceil \log_2 n \rceil \le \log_2 n + 1 \le 9 \log_w n + 1$. For $w > 512$, write $B = 2^b$ with $b = \lfloor (\log_2 w - 4)/5 \rfloor \ge 1$; then $\log_2 w < 5b + 9$, so $\log_2 w / \log_2 B < 5 + 9/b \le 14$.

## Depends on

- [Static multiway predecessor tree with cached minima](multiway-predecessor-tree.md)
- [Fusion node](fusion-node.md)

## Proof depends on

- [Collision-free multiplication for approximate sketches](collision-free-multiplication.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
