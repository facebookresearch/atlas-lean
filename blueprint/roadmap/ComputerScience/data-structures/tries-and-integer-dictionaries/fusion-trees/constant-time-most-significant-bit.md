# Most significant bit in a constant number of word operations

For a word size $w$ and $x \in [1, 2^w)$, the index of the most significant set bit of $x$ can be computed with a constant number of additions, subtractions, multiplications, bitwise Boolean operations and shifts, independently of $w$. The computation splits $x$ into $\lceil \sqrt{w} \rceil$ clusters of $\lceil \sqrt{w} \rceil$ bits, marks the nonzero clusters, compresses the markers into one cluster by a multiplication, finds the most significant marker and then the most significant bit within the selected cluster, each by a parallel comparison against packed powers of two.

## Proof sketch

Each step is a packed computation on fields of $O(\sqrt{w})$ bits with guard bits: testing clusters for nonzero values uses one subtraction per field, compressing the markers uses a multiplier with collision-free shifts, and finding the most significant set bit of a $\sqrt{w}$-bit field counts how many of its packed powers of two it exceeds.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Parallel comparison of packed sketches](parallel-comparison-of-packed-sketches.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
