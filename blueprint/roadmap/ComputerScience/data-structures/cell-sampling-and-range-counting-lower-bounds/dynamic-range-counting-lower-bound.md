# Larsen's lower bound for dynamic range counting

Every dynamic cell-probe structure for two-dimensional weighted orthogonal range counting with $n$ insertions of points carrying $\Theta(\lg n)$-bit weights, $w$-bit cells, $w = \Omega(\lg n)$, and worst-case update time $t_u$ has expected average query time $t_q = \Omega\!\left(\left(\frac{\lg n}{\lg(w t_u)}\right)^{2}\right)$ (Theorem 1). With $w = \Theta(\lg n)$ and $t_u = (\lg n)^{O(1)}$ this is $t_q = \Omega\big((\lg n / \lg\lg n)^2\big)$, almost a quadratic improvement over the previous best $\Omega(\lg n)$, and Larsen notes that it is tight for update time $t_u = \Omega(\lg^{2+\varepsilon} n)$, for any constant $\varepsilon > 0$.

## Proof sketch

Take $\beta = (w t_u)^9$. There are $\lfloor\log_\beta n\rfloor$ epochs, and the integer epochs $i$ with $\tfrac{15}{16}\log_\beta n \le i \le \log_\beta n$ qualify for the epoch-wise lemma; there are $\tfrac{1}{16}\log_\beta n - O(1) = \Theta(\log_\beta n)$ of them once $\log_\beta n$ exceeds a constant (for bounded $\log_\beta n$ the claimed bound is trivial), so a random query probes, in expectation, $\Omega(\log_\beta n)$ cells written in each qualifying epoch; the sets of cells attributed to distinct epochs are disjoint because each cell is charged to the epoch of its last write. Summing over the qualifying epochs only gives expected query cost $\Omega((\log_\beta n)^2) = \Omega\big((\lg n / \lg(w t_u))^2\big)$, since $\log_\beta n = \lg n / (9 \lg(w t_u))$.

## Depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Epoch-wise cell sampling for weighted range counting](epochwise-cell-sampling.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
