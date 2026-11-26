# Collision-free multiplication for approximate sketches

Let $b_1 > \dots > b_r$ be bit positions. There are shifts $m_1, \dots, m_r$, each below $r^3$ modulo a common period, such that for the multiplier $m = \sum_j 2^{m_j}$ and any word $y$, the product $(y \wedge \mathrm{mask}) \cdot m$ has all $r^2$ cross terms $b_i + m_j$ at distinct positions, the diagonal terms $b_i + m_i$ appear in decreasing order of $i$ (the order of the $b_i$), and all diagonal terms lie within a window of at most $2 r^4$ bits. Extracting the diagonal bits gives an *approximate sketch* with gaps, which compares exactly like the perfect sketch on every pair of inputs, stored keys or not.

## Proof sketch

Choose the residues $m_j \bmod r^3$ greedily: each new $m_j$ must avoid the at most $r^2 \cdot r$ values $b_i - b_{i'} + m_{j'}$ already used, and fewer than $r^3$ residues are excluded. Then spread the residues by multiples of $r^3$ to order the diagonal terms within a window of length $O(r^4)$. Comparison is preserved because the extracted bits occur in the same order, separated only by zeros.

## Depends on

- [Significant bits and perfect sketch of a key set](perfect-sketch-of-a-key-set.md)

## Proof depends on

- [Perfect sketches preserve the order of stored keys](sketches-preserve-key-order.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
