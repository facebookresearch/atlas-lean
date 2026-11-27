# LRU is a legal cache manager

Let $k$ be a capacity, $c$ a cache given as a list of pages
without repetitions with at most $k$ pages, and $\sigma$ a request sequence. Then the sequence of
events that LRU emits when serving $\sigma$ from $c$ is a run of the cache system with capacity
$k$ from $c$ to the cache LRU holds after serving $\sigma$; the pages requested by these events are
exactly $\sigma$, in order; and the number of misses among these events equals the number of
misses of LRU on $\sigma$ from $c$.
