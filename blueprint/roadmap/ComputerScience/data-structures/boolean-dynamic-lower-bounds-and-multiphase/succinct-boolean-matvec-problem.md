# Succinct Boolean matrix-vector multiplication

In the *succinct Boolean matrix-vector multiplication* problem, an $n \times n$ Boolean matrix $M$ is stored verbatim in $n^2$ read-only bits, and the structure may store $r$ additional bits of preprocessed information. A query is a vector $v \in \{0,1\}^n$, and the answer is the Boolean product $Mv$ (equivalently over $\mathbb{F}_2$ in the parity variant). Such a structure is *systematic*. The upper bound counts the $w$-bit cells probed among the matrix and the $r$ extra bits; the lower bound lets the query read all $r$ extra bits for free and counts only the entries of $M$ it probes. Query algorithms may be randomized, succeeding with probability at least $1 - 1/n$ for every $v$.

## Depends on

- [The online matrix-vector multiplication conjecture](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Static cell-probe structure with space $S$ and query time $t$](../cell-sampling-and-range-counting-lower-bounds/static-cell-probe-structure.md)

## Sources

- Diptarka Chakraborty, Lior Kamma, Kasper Green Larsen, "Tight Cell Probe Bounds for Succinct Boolean Matrix-Vector Multiplication", STOC (2018), arXiv:1711.04467.
- Kasper Green Larsen, Ryan Williams, "Faster Online Matrix-Vector Multiplication", SODA (2017), arXiv:1605.01695.
