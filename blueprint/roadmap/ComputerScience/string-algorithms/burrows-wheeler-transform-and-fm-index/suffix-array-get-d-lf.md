# LF in suffix-array terms

Let $t$ be a text of length $n$ over a linearly ordered alphabet, $SA$ the suffix array of $t$
followed by a sentinel smaller than every letter, and $\mathrm{LF}$ the LF-mapping of the
Burrows–Wheeler transform of $t$. For every row $r \le n$, we have $\mathrm{LF}(r) \le n$ and
$SA[\mathrm{LF}(r)] = (SA[r] + n) \bmod (n + 1)$, that is, $SA[r] - 1$ if $SA[r] > 0$ and $n$ if
$SA[r] = 0$.
