# The recency invariant for a repeated page

Let $k$ be a capacity, $c$ a cache (most
recently used first) and $S$ a list of at most $k$ pages equal to the first $|S|$ pages of $c$.
If $p \in S$, then after one LRU step with capacity $k$ serving $p$, the first $|S|$ pages of the
cache are $p$ followed by $S$ with the first occurrence of $p$ removed.
