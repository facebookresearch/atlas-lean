# Hits do not change the offline strategy's misses

Let $k$ be a capacity, let $c$ be a
cache and let $w$ be a request sequence all of whose requests lie in $c$. Then for every request
sequence $\tau$, the offline strategy with capacity $k$ (on a miss with a full cache, evict the
first cached page not among the next $k - 1$ requests, if there is one) started with cache $c$
misses as many times on $w$ followed by $\tau$ as on $\tau$ alone.
