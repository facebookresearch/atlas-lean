# Fredman–Saks lower bound for dynamic rank

In the cell-probe model with $w$-bit cells, every dynamic rank/select dictionary on $n$ elements whose updates take $t_u$ amortized probes has query time $t_q = \Omega\left(\frac{\log n}{\log(t_u w)}\right)$. In particular, with $w = \Theta(\log U)$ and $t_u = (\log n)^{O(1)}$, queries need $\Omega(\log n / \log\log n)$ probes when $U = n^{O(1)}$, matching Dietz's $O(\log n / \log\log n)$ word-RAM structure.

## Proof sketch

A dynamic rank structure solves dynamic prefix parity over a bit array of length $n$ by storing the set of positions holding a one. The chronogram method partitions the update sequence into epochs of geometrically growing lengths and shows that a random query must read a cell written in a constant fraction of the epochs, each read accounting for $\Omega(1)$ epochs only when epoch lengths grow by a factor of $\Theta(t_u w)$.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)

## Sources

- Michael L. Fredman, Michael E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", STOC (1989).
- Paul F. Dietz, "Optimal Algorithms for List Indexing and Subset Rank", WADS (1989).
