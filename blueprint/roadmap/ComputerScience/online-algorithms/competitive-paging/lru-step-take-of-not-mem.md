# The recency invariant for a new page

Let $k$ be a capacity, $c$ a cache (most recently
used first) and $S$ a list with $|S| + 1 \le k$ equal to the first $|S|$ pages of $c$. If
$p \notin S$, then after one LRU step with capacity $k$ serving $p$, the first $|S| + 1$ pages of
the cache are $p$ followed by $S$.
