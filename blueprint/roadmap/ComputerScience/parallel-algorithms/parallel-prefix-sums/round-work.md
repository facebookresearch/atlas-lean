# Work of a scan round

The work of round $k$ on $n$ positions is $\max(n - 2^k, 0)$, the
number of positions $i < n$ with $i \ge 2^k$, each of which performs one multiplication.
