# LRU misses at most $k - |S|$ times in the rest of a phase

Let $k$ be a capacity, $c$ a
cache (most recently used first) and $S$ a duplicate-free list of at most $k$ pages equal to the
first $|S|$ pages of $c$. For every request sequence $\sigma$, let $\pi$ be the phase that the
phase split cuts from $\sigma$ with $S$ as the pages already in the phase: the longest prefix of
$\sigma$ whose distinct pages, together with those of $S$, number at most $k$. Then the number of
LRU misses with capacity $k$ serving $\pi$ from $c$, plus $|S|$, is at most $k$.
