# FIFO is `k`-competitive against the offline optimum

Let $k \ge 1$, let $\sigma$ be a
finite request sequence, and let $c_0$ be a list of at most $k$ distinct pages. Let $m$ be the
number of misses of the furthest-in-future manager with capacity $k$ serving $\sigma$ from the
cache $c_0$. Then the FIFO online pager with capacity $k$, started in any legal cache (at most
$k$ distinct pages), misses at most $k m + k$ of the requests of $\sigma$.
