# Each LRU step is a legal transition

Let $k$ be a capacity and $c$ a duplicate-free cache
with at most $k$ pages. For every page $p$, the cache system with capacity $k$ has a transition
from $c$, labelled by the LRU event for $p$ at $c$, to the cache produced by one LRU step with
capacity $k$ serving $p$.
