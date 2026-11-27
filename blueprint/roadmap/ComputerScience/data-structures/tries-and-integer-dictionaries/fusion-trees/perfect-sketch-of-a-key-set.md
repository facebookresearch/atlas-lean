# Significant bits and perfect sketch of a key set

Let $x_1 < x_2 < \dots < x_k$ be $w$-bit keys. For each adjacent pair, the most significant bit position at which $x_i$ and $x_{i+1}$ differ is a *significant bit*; let $b_1 > \dots > b_r$ be the distinct significant bits, so $r \le k - 1$. The *perfect sketch* of a word $y$ is the $r$-bit word $\mathrm{sketch}(y) = (y_{b_1}, y_{b_2}, \dots, y_{b_r})$ obtained by extracting these bits in order.

## Depends on

- [Static predecessor problem on word keys](static-predecessor-problem.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
