# Resource-augmented competitiveness of LRU

Let $1 \le h \le k$. Let LRU run with a fast memory of $k$ pages, starting from any list $c$ of pages as its cache (most recently used first), and let the offline optimum MIN, the furthest-in-future manager, run with a fast memory of $h$ pages, starting from any cache $c_0$ of at most $h$ pages without repetition. For every request sequence $s$, $(k - h + 1) F_{\mathrm{LRU}}(s) \le k F_{\mathrm{MIN}}(s) + (k - h + 1) h$, that is, $F_{\mathrm{LRU}}(s) \le \frac{k}{k - h + 1} F_{\mathrm{MIN}}(s) + h$, where $F$ counts page faults.

## Remarks

With $k = 2h$ the bound gives $F_{\mathrm{LRU}}(s) \le 2 F_{\mathrm{MIN}}(s) + h$.

The additive term $h$ reflects that the two fast memories may start with different pages, so that LRU may fault $h$ times before MIN faults at all. Suppose that $c$ is a fast memory for LRU, that is, it has at most $k$ pages and no repetition, and that it contains all the pages of $c_0$ and no others more recently used, so that its first $|c_0|$ entries are the pages of $c_0$. Then the additive term can be dropped: $(k - h + 1) F_{\mathrm{LRU}}(s) \le k F_{\mathrm{MIN}}(s)$. This covers the case where both start empty.

Unlike the bound with the additive term, which holds for any list $c$, this one is stated only for such a fast memory: for a list with a repeated page, containing exactly the pages of $c_0$ is not enough. With $k = 3$, $h = 2$, distinct pages $a$, $b$ and $x$, $c = (a, a, b)$, $c_0 = \{a, b\}$ and $s = (x, b)$, serving $x$ faults, puts $x$ in front and keeps the first three entries, $(x, a, a)$, so LRU faults again on $b$, while MIN faults only on $x$; then $(k - h + 1) F_{\mathrm{LRU}}(s) = 4 > 3 = k F_{\mathrm{MIN}}(s)$.

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized efficiency of list update and paging rules", *Communications of the ACM* 28(2):202–208, 1985, Section 4, Theorem 6 and the remarks after its proof
