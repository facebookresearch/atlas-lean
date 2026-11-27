# A policy that misses at most $k$ times per phase is $k$-competitive

Let $k \ge 1$ and
consider a paging policy on list caches, given by its step function. Suppose that, started from
any cache, the policy misses at most $k$ times on the first phase of every request sequence (the
longest prefix of the sequence with at most $k$ distinct pages). Let $T$ be a legal trace of
caching with capacity $k$ (a run of the cache transition system) whose initial cache is a list of
at most $k$ pages with no page repeated, and let $m$ be the number of misses in $T$. Then, started
from any cache, the policy misses at most $km + k$ times on the sequence of requests served by
$T$.
