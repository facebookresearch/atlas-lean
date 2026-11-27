# Resource-augmented competitiveness of LRU

Let $1 \le h \le k$. Let LRU run with a fast memory of $k$ pages, starting from any list $c$ of pages as its cache (most recently used first), and let the offline optimum MIN, the furthest-in-future manager, run with a fast memory of $h$ pages, starting from any cache $c_0$ of at most $h$ pages without repetition. For every request sequence $s$, $(k - h + 1) F_{\mathrm{LRU}}(s) \le k F_{\mathrm{MIN}}(s) + (k - h + 1) h$, that is, $F_{\mathrm{LRU}}(s) \le \frac{k}{k - h + 1} F_{\mathrm{MIN}}(s) + h$, where $F$ counts page faults.

## Remarks

With $k = 2h$ the bound gives $F_{\mathrm{LRU}}(s) \le 2 F_{\mathrm{MIN}}(s) + h$.

The additive term $h$ reflects that the two fast memories may start with different pages, so that LRU may fault $h$ times before MIN faults at all. If LRU's fast memory initially contains all the pages in MIN's fast memory and no others more recently used, as when both start empty, the additive term can be dropped.

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized efficiency of list update and paging rules", *Communications of the ACM* 28(2):202–208, 1985, Section 4, Theorem 6 and the remarks after its proof
