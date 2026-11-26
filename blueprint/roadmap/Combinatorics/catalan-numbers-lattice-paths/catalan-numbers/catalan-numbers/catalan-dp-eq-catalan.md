# The bottom-up table computes the Catalan numbers

For a natural number $n$ let $T(n)$ be the list of natural numbers defined by $T(0) = [1]$ and, for $p = T(n)$, $T(n+1) = p$ followed by one more entry, the sum of the products of corresponding entries of $p$ and of its reverse (pairing entries up to the length of the shorter list). Then for every natural number $n$, the entry of $T(n)$ at position $n$ (positions counted from $0$, default value $0$) is the Catalan number $C_n$.
