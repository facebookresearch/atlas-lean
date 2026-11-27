# Patrascu-Demaine logarithmic cell-probe lower bound for dynamic connectivity

In the cell-probe model with cells of $w = \Theta(\log n)$ bits, let $t_u$ and $t_q$ be the amortized expected update and query times of any data structure for fully dynamic connectivity on $n$ vertices that may use amortization, nondeterministic queries and Las Vegas randomization, or Monte Carlo randomization with error probability $n^{-\Omega(1)}$ (already for graphs that are always disjoint unions of paths). Then

$$
t_q \lg\Bigl(\frac{t_u}{t_q}\Bigr) = \Omega(\lg n) \quad \text{and} \quad t_u \lg\Bigl(\frac{t_q}{t_u}\Bigr) = \Omega(\lg n),
$$

where $\lg x$ denotes $\log_2(2 + x)$, which is positive for all $x \ge 0$ (Theorem 2.4). In particular $\max\{t_u, t_q\} = \Omega(\log n)$.

## Proof sketch

The proof introduces the information-transfer technique: fix a random sequence of operations arranged as the leaves of a balanced binary tree over time, and for each node count the cells written during its left subtree and read during its right subtree. Encoding arguments show that this transfer must be large, since the queries in the right half reveal the random permutations inserted in the left half of a grid-graph instance made of disjoint paths. Summing over the $\Theta(\log n)$ tree levels gives the trade-off.

## Depends on

- [The cell-probe model](../../range-query-structures/advanced-data-structures/the-cell-probe-model.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)
- [Amortized update and query cost of a dynamic cell-probe structure](../../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Proof depends on

- [Information transfer must carry the entropy of the interleaved updates](../../dynamic-information-transfer-lower-bounds/transfer-entropy-bound.md)
- [Partial sums over permutation groups reduce to connectivity of disjoint paths](../../dynamic-information-transfer-lower-bounds/grid-permutation-reduction.md)

## Sources

- Mihai Patrascu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM J. Comput. 35(4) (2006), arXiv:cs/0502041.
