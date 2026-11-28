# Catalan number read from the bottom-up table

For a natural number $n$ let $T(n)$ be the list of natural numbers defined by $T(0) = [1]$ and, for $p = T(n)$, $T(n+1) = p$ followed by one more entry, the sum of the products of corresponding entries of $p$ and of its reverse (pairing entries up to the length of the shorter list). For a natural number $n$, the value read from the table is the entry of $T(n)$ at position $n$, positions counted from $0$, with the default value $0$ if $T(n)$ has no such entry.
