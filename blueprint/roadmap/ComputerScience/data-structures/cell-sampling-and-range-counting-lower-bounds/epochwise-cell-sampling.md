# Epoch-wise cell sampling for weighted range counting

Fix a deterministic dynamic structure for two-dimensional weighted orthogonal range counting with $w$-bit cells and worst-case update time $t_u$, and set $\beta = (w t_u)^9$, so that $\log_\beta n = \lg n / (9\lg(w t_u))$. There is a hard distribution of the following form. Epochs $i = \lfloor\log_\beta n\rfloor, \dots, 2, 1$ are executed in this order, and epoch $i$ inserts the $m_i$ points of the Fibonacci lattice $F_{m_i}$, where $m_i = \Theta(\beta^i)$ is a Fibonacci number, with coordinates scaled by a factor of about $n/m_i$ (rounded to integers) to fit $[n] \times [n]$; each point gets an independent uniformly random weight from $[\Delta]$, where $\Delta$ is the largest prime below $n^4$. After epoch $1$ a uniformly random query $q \in [n] \times [n]$ is asked. Charge each cell to the epoch of its last write and let $t_i(U, q)$ be the number of cells charged to epoch $i$ that the query algorithm probes on $q$ after the update sequence $U$. Then $\mathbb{E}[t_i(U, q)] = \Omega(\log_\beta n)$ for every integer epoch $i$ with $\tfrac{15}{16}\log_\beta n \le i \le \log_\beta n$, where the expectation is over the random weights and the random query. (The source writes the construction with epoch sizes exactly $\beta^i$, each a Fibonacci number dividing $n$, and notes that these are conveniences removable by adjusting constants.)

## Proof sketch

Updates after epoch $i$ write at most $t_u \sum_{j < i} m_j = O(t_u \beta^{i-1})$ cells, few compared with the $m_i = \Theta(\beta^i)$ insertions of epoch $i$, so information about epoch $i$ must be read from cells written during it. If queries probed $o(\log_\beta n)$ such cells in expectation, the cell-sampling lemma applied to the cells of epoch $i$ would resolve a set of queries whose incidence vectors on the scaled Fibonacci lattice of epoch $i$ are linearly independent over $[\Delta]$ (by the uniformity of the lattice), so their answers reveal more information about the epoch's weights than the sample can encode. Concretely, Lemma 6 gives $O(\beta^{i-1} w)$ cells of epoch $i$ that resolve $\Omega(\beta^{i-3/4})$ such queries, and an encoding of the epoch's weights through them beats $H(\mathbf{U}_i)$ by $\Omega(\beta^{i-3/4}\lg\Delta)$ bits. The restriction $i \ge \tfrac{15}{16}\log_\beta n$ is used inside the proof of Lemma 6, in a second encoding argument (Lemma 8) about a random set of queries, where it bounds the cost of describing the grid cells those queries hit.

## Depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Cell-sampling lemma](cell-sampling-lemma.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
