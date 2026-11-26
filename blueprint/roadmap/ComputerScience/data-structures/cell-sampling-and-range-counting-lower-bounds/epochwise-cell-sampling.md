# Epoch-wise cell sampling for weighted range counting

Fix a deterministic dynamic structure for two-dimensional weighted orthogonal range counting with $w$-bit cells and worst-case update time $t_u$, and set $\beta = (w t_u)^9$, so that $\log_\beta n = \lg n / (9\lg(w t_u))$; assume, as in the source, that each $\beta^i$ is a Fibonacci number dividing $n$. In the hard distribution, epochs $i = \log_\beta n, \dots, 2, 1$ are executed in this order, and epoch $i$ inserts the $\beta^i$ points of the Fibonacci lattice $F_{\beta^i}$ scaled by $n/\beta^i$ to fit $[n] \times [n]$, each with an independent uniformly random weight from $[\Delta]$, where $\Delta$ is the largest prime below $n^4$; after epoch $1$ a uniformly random query $q \in [n] \times [n]$ is asked. Charge each cell to the epoch of its last write and let $t_i(U, q)$ be the number of cells charged to epoch $i$ that the query algorithm probes on $q$ after the update sequence $U$. Then $\mathbb{E}[t_i(U, q)] = \Omega(\log_\beta n)$ for every epoch $i$ with $\tfrac{15}{16}\log_\beta n \le i \le \log_\beta n$, where the expectation is over the random weights and the random query.

## Proof sketch

Updates after epoch $i$ write at most $t_u \sum_{j < i} \beta^j = O(t_u \beta^{i-1})$ cells, few compared with the $\beta^i$ insertions of epoch $i$, so information about epoch $i$ must be read from cells written during it. If queries probed $o(\log_\beta n)$ such cells in expectation, the cell-sampling lemma applied to the cells of epoch $i$ would resolve a set of queries whose incidence vectors on the scaled Fibonacci lattice of epoch $i$ are linearly independent over $[\Delta]$ (by the uniformity of the lattice), so their answers reveal more information about the epoch's weights than the sample can encode. The restriction $i \ge \tfrac{15}{16}\log_\beta n$ is what makes the description of the sampled query set shorter than its entropy in this encoding argument.

## Depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Cell-sampling lemma](cell-sampling-lemma.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
