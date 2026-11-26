# Convolution-3SUM reduces to Exact Triangle

For every $t \ge 1$ there is an explicit map sending a Convolution-3SUM instance of length $N \le t^2$ to $2t$ Exact Triangle instances, each with exactly $t$ vertices per part and weights bounded by a constant times the input magnitude, such that the Convolution-3SUM instance has a solution if and only if one of the Exact Triangle instances has a zero triangle. With $t = \lfloor \sqrt{N} \rfloor + 1$ this gives $O(\sqrt{N})$ instances on $O(\sqrt{N})$ vertices per part, so an $O(t^{3 - \epsilon})$ Exact Triangle algorithm gives an $O(N^{2 - \epsilon/2})$ Convolution-3SUM algorithm.

## Proof sketch

Write indices as $i = i_1 t + i_2$. For each carry bit and each value of the high digit of the first index, encode the low digits as vertices of the three parts and put $X$, $Y$ and $-Z$ values on the three edge sets so that a zero triangle reads off $X[i] + Y[j] = Z[i+j]$.

## Depends on

- [Convolution-3SUM](../three-sum-reductions/convolution-three-sum.md)
- [Exact Triangle](exact-triangle-problem.md)
- [Fine-grained reductions](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/fine-grained-reductions.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Finding, Minimizing, and Counting Weighted Subgraphs", SIAM Journal on Computing 42(3), 2013.
- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
