# Larsen's lower bound for dynamic range counting

Every dynamic cell-probe structure for two-dimensional weighted orthogonal range counting with $n$ insertions, $w$-bit cells and worst-case update time $t_u$ has query time $t_q = \Omega\!\left(\left(\frac{\lg n}{\lg(w t_u)}\right)^{2}\right)$. With $w = \Theta(\lg n)$ and $t_u = (\lg n)^{O(1)}$ this is $t_q = \Omega\big((\lg n / \lg\lg n)^2\big)$, almost a quadratic improvement over the previous best $\Omega(\lg n)$, and it is tight for $t_u = \lg^{2 + \Omega(1)} n$.

## Proof sketch

Take $\beta = (w t_u)^9$. There are $\log_\beta n$ epochs, and the $\log_\beta n - \lceil \tfrac{15}{16}\log_\beta n \rceil + 1 = \Theta(\log_\beta n)$ epochs $i \ge \tfrac{15}{16}\log_\beta n$ qualify for the epoch-wise lemma, so a random query probes, in expectation, $\Omega(\log_\beta n)$ cells written in each qualifying epoch; the sets of cells attributed to distinct epochs are disjoint because each cell is charged to the epoch of its last write. Summing over the qualifying epochs only gives expected query cost $\Omega((\log_\beta n)^2) = \Omega\big((\lg n / \lg(w t_u))^2\big)$, since $\log_\beta n = \lg n / (9 \lg(w t_u))$. A range-tree style structure with fan-out $\lg^{\Omega(1)} n$ over a dominance counting structure achieves the matching query time with $\lg^{2+\Omega(1)} n$ update time.

## Depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Epoch-wise cell sampling for weighted range counting](epochwise-cell-sampling.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
- Joseph JaJa, Christian W. Mortensen, Qingmin Shi, "Space-Efficient and Fast Algorithms for Multidimensional Dominance Reporting and Counting", ISAAC (2004).
