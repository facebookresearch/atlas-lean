# Logarithmic-base-B lower bound for dynamic problems in external memory

In the external-memory model with blocks of $B$ words of $\Theta(\lg n)$ bits, viewed as a cell-probe model with cells of $B \cdot \Theta(\lg n)$ bits, every structure for dynamic connectivity, even on graphs that are always disjoint unions of paths, has $\max\{t_u, t_q\} = \Omega(\log_B n)$ amortized I/Os (Theorem 2.5, allowing amortization, Las Vegas randomization and nondeterminism), without any assumption on how the structure manipulates data. The same $\Omega(\log_B n)$ holds for partial sums with $\delta = \Theta(\lg n)$-bit updates and $b = B \lg n$-bit cells (Theorem 2.2). For forests, Euler-tour trees combined with buffer trees give a matching $O(\log_B n)$.

## Proof sketch

With $b$-bit cells, the basic information-transfer argument shows only that $\Omega(\delta \lg n / b)$ bits' worth of reads, that is $\Omega(\lg n / B)$ cell reads, are needed. Pătraşcu and Demaine (Section 7) instead use random query indices and compare each right interval containing $L$ queries with $BL$ random queries that could be asked at a random time $t$ in it; their answers carry $\Omega(BL\delta) = \Omega(Lb)$ bits about the left interval. If few reads of the right interval hit cells written in the left one, most of these simulated queries read no such cell, so the information must already be in the few cells read, each of $b$ bits. An encoding that lists those cells and a succinct separator between the cells read and the cells written shows that $\Omega(L) - O(s)$ such reads occur, for a lower-order term $s$, and summing over a tree whose nodes span $\Theta(\log_B n)$ levels gives the bound.

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
