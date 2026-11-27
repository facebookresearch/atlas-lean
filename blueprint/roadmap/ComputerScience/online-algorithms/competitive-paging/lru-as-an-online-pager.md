# LRU as an online pager

Let $\alpha$ be a type of pages and $k \in \mathbb{N}$. LRU as an online pager with cache size $k$
has as states the lists of at most $k$ pages (most recently used first), the empty list as
initial state, the list itself as the cache of a state, and as step the LRU step with capacity
$k$: serving a request for $p$ in state $c$ moves $p$ to the front, giving $p$ followed by $c$
with its first occurrence of $p$ removed, and keeps only the first $k$ pages of the result.
