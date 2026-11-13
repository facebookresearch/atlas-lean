# The ratio `k` is tight for FIFO

Let $k \ge 1$ and let $c$ and $d$ be natural numbers
with $c < k d$. For every natural number $b$ there is a finite request sequence $\sigma$ over
$k + 1$ pages with $c \cdot m + b < d \cdot f$, where $m$ is the number of misses of the
furthest-in-future manager with capacity $k$ serving $\sigma$ from the empty cache, and $f$ is
the number of misses of the FIFO online pager with capacity $k$ serving $\sigma$ from its initial,
empty cache.

So no ratio $c / d < k$ makes FIFO $c / d$-competitive, whatever the additive constant.
