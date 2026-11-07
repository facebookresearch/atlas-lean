# Cost of Boyer–Moore preprocessing

For a pattern of length $m$ over an alphabet of size
$\sigma$, the event cost of the Boyer–Moore preprocessing is at most $\sigma$ when $m = 0$ and at
most $\sigma + 10m - 6$ when $m \ge 1$.

The cost counts the selected events of the preprocessor, including initialization of the
alphabet table; it is not a word-RAM or bit-cost bound.
