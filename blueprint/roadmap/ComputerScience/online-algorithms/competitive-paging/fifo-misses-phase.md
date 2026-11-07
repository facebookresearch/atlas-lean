# FIFO misses at most `k` times per phase

Let $S$ be a list of at most $k$ distinct pages
(the pages already in the current phase), let $c$ be any list of pages (a FIFO cache, oldest page
first), and let $L$ be a list of distinct pages, each of them in $S$, that is a suffix of $c$. For
every request sequence $\sigma$, let $P$ be the phase split off from $\sigma$ given $S$: the
longest prefix of $\sigma$ whose distinct pages, together with those of $S$, number at most $k$.
Then the number of misses of the FIFO step policy with capacity $k$ serving $P$ from $c$, plus the
length of $L$, is at most $k$.

The pages loaded so far in the phase ($L$, in load order) stay at the back of the queue: each
miss appends one, and an eviction removes the front, which is not among them while at most $k$
pages have been loaded. So a page of the phase is missed at most once, and a phase has at most
$k$ distinct pages.
