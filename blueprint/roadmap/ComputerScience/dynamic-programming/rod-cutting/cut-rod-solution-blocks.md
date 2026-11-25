# Reconstructed pieces are the saved first cuts

Let $p$ be a price vector of length $n$
with entries in an additive commutative monoid carrying a linear order. Let $s$ be the vector of
saved first cuts computed by the extended bottom-up rod-cutting algorithm, of length $n$, whose
entry $j - 1$ is the cut saved for length $j$, and let $(b_0, \dots, b_{m-1})$ be the composition
of $n$ returned by the rod-cutting reconstruction. For every $i < m$, the index
$n - (b_0 + \dots + b_{i-1}) - 1$ lies within $s$ and the entry of $s$ at this index is $b_i$:
the $i$-th piece is the first cut saved for the remaining length $n - (b_0 + \dots + b_{i-1})$.
