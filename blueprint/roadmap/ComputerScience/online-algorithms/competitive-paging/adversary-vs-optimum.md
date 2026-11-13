# The adversary forces $n$ misses while the optimum misses at most $k + \lceil n / k \rceil$ times

**The adversary forces $n$ misses while the optimum misses at most $k + \lceil n / k \rceil$
times.** Let $k \ge 1$ and let $A$ be a deterministic online pager with cache size $k$ on the
$k + 1$ pages $0, \dots, k$. For every $n$, on the adversary's sequence of $n$ requests started
from the initial state of $A$, the pager $A$ started in its initial state misses exactly $n$
times, and the furthest-in-future strategy with capacity $k$ started with an empty cache misses
at most $k + \lceil n / k \rceil$ times.
