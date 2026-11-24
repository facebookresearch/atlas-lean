# LRU is $k$-competitive against the offline optimum

Let $k \ge 1$, and let $c$ and $c_0$
be duplicate-free caches with at most $k$ pages each. For every request sequence $\sigma$, the
trace that LRU with capacity $k$ emits when serving $\sigma$ from $c$ has at most $k m + k$
misses, where $m$ is the number of misses of the furthest-in-future manager with capacity $k$
serving $\sigma$ from $c_0$.

Furthest-in-future misses no more often than any legal trace serving the same requests from the
same cache, so it is the offline optimum.
