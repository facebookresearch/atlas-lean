# Fusion node

A *fusion node* stores $k \le B$ keys $x_1 < \dots < x_k$ of $w$ bits together with the parameters of their approximate sketches (the significant-bit mask and the multiplier) and the word that packs their approximate sketches with guard bits. Here $B$ is a branching factor with $B^5 = O(w)$, so that the packed sketches fit in one word. A query computes the approximate sketch of $q$, its packed rank by parallel comparison, the corrected query word, and its packed rank again, returning the inclusive rank of $q$ among the node's keys.

## Depends on

- [Significant bits and perfect sketch of a key set](perfect-sketch-of-a-key-set.md)
- [Collision-free multiplication for approximate sketches](collision-free-multiplication.md)
- [Parallel comparison of packed sketches](parallel-comparison-of-packed-sketches.md)
- [Recovering the rank of an arbitrary query from sketch ranks](sketch-rank-correction.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
