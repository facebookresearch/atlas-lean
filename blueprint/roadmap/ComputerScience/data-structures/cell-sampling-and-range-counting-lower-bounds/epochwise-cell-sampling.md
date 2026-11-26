# Epoch-wise cell sampling for weighted range counting

Let $\beta = (w t_u)^2$ and divide a random sequence of $n$ weighted insertions, read backwards from the final query, into epochs $i = 1, 2, \dots$ of $\beta^i$ insertions each, with points chosen from a grid tailored to epoch $i$. For every epoch $i$ with $\beta^i \le n$, a uniformly random query must, in expectation, probe $\Omega\big(\log_{\beta} n\big)$ cells whose most recent write occurred in epoch $i$, where $\log_\beta n = \lg n / \lg(w t_u)$.

## Proof sketch

Updates after epoch $i$ write at most $t_u \sum_{j < i} \beta^j = O(t_u \beta^{i-1})$ cells, few compared with the $\beta^i$ insertions of epoch $i$, so information about epoch $i$ must be read from cells written during it. If queries probed $o(\log_\beta n)$ such cells, the cell-sampling lemma applied to the cells of epoch $i$ would resolve a set of queries whose answers, by the geometry of the epoch's grid (a static range counting instance with $\Theta(\lg n)$-bit weights, where answers behave like polynomial evaluations), reveal more information about the epoch's weights than the sample can encode.

## Depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Proof depends on

- [Dynamic weighted orthogonal range counting](weighted-dominance-range-counting.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
