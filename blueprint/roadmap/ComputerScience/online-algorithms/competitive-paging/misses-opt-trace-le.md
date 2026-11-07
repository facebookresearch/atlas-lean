# The offline trace misses at most once every $k$ requests

Let $k \ge 1$ and consider the
$k + 1$ pages $0, 1, \dots, k$. Let $N$ be a natural number, $\sigma$ a sequence of $n \le N$
requests to these pages, and $c$ a cache of $|c| \le k$ distinct pages. Then the number of misses
of the offline trace with cache size $k$ from $c$ on $\sigma$ is at most
$(k - |c|) + \lfloor (n + k - 1) / k \rfloor = (k - |c|) + \lceil n / k \rceil$: after at most
$k - |c|$ misses filling the cache, at most one miss every $k$ requests.
