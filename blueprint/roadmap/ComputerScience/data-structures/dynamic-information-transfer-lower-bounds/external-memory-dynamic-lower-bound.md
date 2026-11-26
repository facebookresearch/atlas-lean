# Logarithmic-base-B lower bound for dynamic problems in external memory

In the external-memory model with blocks of $B$ words of $\Theta(\lg n)$ bits, viewed as a cell-probe model with cells of $B \cdot \Theta(\lg n)$ bits, every structure for dynamic partial sums or dynamic connectivity has $\max\{t_u, t_q\} = \Omega(\log_B n)$ amortized I/Os, without any assumption on how the structure manipulates data. This matches B-trees.

## Proof sketch

Run the information-transfer argument with cell size $w' = B w$: the encoding of a node's transfer now costs $|\mathrm{IT}(v)| \cdot (Bw + \lg m)$ bits while the entropy to be transferred is unchanged, so the bound per tree level shrinks by a factor $B$; grouping $\lg B$ levels of the information-transfer tree into one superlevel restores constant transfer per superlevel, and there are $\Theta(\log_B n)$ superlevels.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](../disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/fully-dynamic-connectivity-problems.md)
- [The external-memory model](../../memory-hierarchy-algorithms/external-memory-algorithms/the-external-memory-model.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)
- [Amortized update and query cost of a dynamic cell-probe structure](amortized-cell-probe-costs.md)

## Proof depends on

- [Pătraşcu–Demaine tradeoff for dynamic partial sums](partial-sums-tradeoff.md)
- [Information transfer must carry the entropy of the interleaved updates](transfer-entropy-bound.md)
- [Partial sums over permutation groups reduce to connectivity of disjoint paths](grid-permutation-reduction.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
