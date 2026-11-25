# The LF step moves one position left in the text

Let $t$ be a text of length $n$ over a linearly ordered alphabet, $SA$ the suffix array of $t$
followed by a sentinel smaller than every letter, and $\mathrm{LF}$ the LF-mapping of the
Burrows–Wheeler transform of $t$. For every row $r \le n$ with $SA[r] > 0$,
$SA[r] = SA[\mathrm{LF}(r)] + 1$.
