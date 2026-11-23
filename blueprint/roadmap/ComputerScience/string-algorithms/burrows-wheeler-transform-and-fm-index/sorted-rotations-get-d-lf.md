# The LF-mapping property

Let $t$ be a text of length $n$ over a linearly ordered alphabet, $R$ the list of sorted rotations
of $t$ and $\mathrm{LF}$ the LF-mapping of the Burrows–Wheeler transform of $t$. For every row
$r \le n$, we have $\mathrm{LF}(r) \le n$ and $R[\mathrm{LF}(r)] = (R[r] + n) \bmod (n + 1)$: row
$\mathrm{LF}(r)$ holds the rotation of row $r$ rotated right by one position, starting one
position earlier in the text, cyclically.
