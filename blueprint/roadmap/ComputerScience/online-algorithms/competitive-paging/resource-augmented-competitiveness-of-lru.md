# Resource-augmented competitiveness of LRU

Let $1 \le h \le k$. Let LRU run with a fast memory of $k$ pages and the offline optimum MIN with a fast memory of $h$ pages, both starting with empty fast memory. For every request sequence $s$, $F_{\mathrm{LRU}}(s) \le \frac{k}{k - h + 1} F_{\mathrm{MIN}}(s) + h$, where $F$ counts page faults. In particular, with $k = 2h$, $F_{\mathrm{LRU}}(s) \le 2 F_{\mathrm{MIN}}(s) + h$.

## Depends on

- [Number of misses in a trace](../../greedy-algorithms-and-matroids/furthest-in-future-caching/misses.md)
- [Deterministic online paging algorithm](deterministic-online-paging-algorithm.md)

## Proof depends on

- [Furthest-in-future caching has the fewest misses](../../greedy-algorithms-and-matroids/furthest-in-future-caching/furthest-in-future-misses-le.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized efficiency of list update and paging rules", *Communications of the ACM* 28(2):202–208, 1985, Section 4, Theorem 6
