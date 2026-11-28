# Fredman–Saks lower bound for dynamic rank

In the cell-probe model with $w$-bit cells, $w \ge \log_2 n$, every data structure for dynamic prefix parity over an array of $n$ bits (flip a bit; report the parity of a prefix) whose updates take $t_u$ amortized probes has query time $t_q = \Omega\left(\frac{\log n}{\log w + \log t_u}\right)$. A dynamic rank/select dictionary over the universe $[n]$ solves this problem, so the same bound holds for it, and hence for dictionaries over any universe $[U]$ with $U \ge n$ that may store $n$ keys. In particular, with $w = \Theta(\log U)$, $U = n^{O(1)}$ and $t_u = (\log n)^{O(1)}$, queries need $\Omega(\log n / \log\log n)$ probes, matching Dietz's $O(\log n / \log\log n)$ word-RAM structure.

## Proof sketch

Store the set of positions holding a one; the parity of a prefix is the rank of the prefix end modulo $2$. The chronogram method splits the update history before a query into epochs whose lengths grow geometrically by a factor polynomial in $t_u w$; few cells are written in the later, shorter epochs, so they cannot encode the effect of an epoch's updates, and a random query must probe a cell last written in each of a constant fraction of the $\Omega(\log n / \log(t_u w))$ epochs.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)

## Sources

- Michael L. Fredman, Michael E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", STOC (1989).
- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
- Paul F. Dietz, "Optimal Algorithms for List Indexing and Subset Rank", WADS (1989).
