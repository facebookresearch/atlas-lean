# Cache after LRU serves a request sequence

For a capacity $k$, a cache $c$ (a list of
pages, most recently used first) and a request sequence $\sigma$, this is the cache obtained from
$c$ by applying one LRU step with capacity $k$ for each request of $\sigma$, in order.
