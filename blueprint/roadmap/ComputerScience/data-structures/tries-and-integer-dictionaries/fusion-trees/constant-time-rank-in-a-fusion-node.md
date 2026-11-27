# Constant-time rank in a fusion node

For every word size $w$ and every fusion node with fitting parameters, the inclusive rank of any $w$-bit query among the node's keys is computed by a fixed sequence of $O(1)$ word-RAM instructions (multiplications, Boolean operations, shifts, subtractions and two loads of neighbouring full keys), independent of $w$ and of the keys.

## Proof sketch

Compute the approximate sketch by masking and multiplying, rank it among the packed sketches by one parallel comparison, load the two neighbouring keys, choose the one with the smaller exclusive or, compute the most significant differing bit in constant time, form the corrected word, and rank its sketch once more.

## Depends on

- [Fusion node](fusion-node.md)

## Proof depends on

- [Parallel comparison of packed sketches](parallel-comparison-of-packed-sketches.md)
- [Recovering the rank of an arbitrary query from sketch ranks](sketch-rank-correction.md)
- [Most significant bit in a constant number of word operations](constant-time-most-significant-bit.md)
- [Collision-free multiplication for approximate sketches](collision-free-multiplication.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
