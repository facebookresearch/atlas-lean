# FIFO is `k`-competitive

**FIFO is `k`-competitive** (Sleator and Tarjan). Let $k \ge 1$, and let $\tau$ be a legal
trace of the caching system with capacity $k$ that starts from a cache $c_0$ of at most $k$
distinct pages; let $m$ be its number of misses. Then the FIFO online pager with capacity $k$,
started in any legal cache (at most $k$ distinct pages) and serving the requests of $\tau$ in
order, misses at most $k m + k$ times.
