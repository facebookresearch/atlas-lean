# The bottom-up table lists the first Catalan numbers

For a natural number $n$ let $T(n)$ be the list of natural numbers defined by $T(0) = [1]$ and, for $p = T(n)$, $T(n+1) = p$ followed by one more entry, the sum of the products of corresponding entries of $p$ and of its reverse (pairing entries up to the length of the shorter list). Then for every natural number $n$, $T(n) = [C_0, C_1, \dots, C_n]$, where $C_k$ is the $k$-th Catalan number ($C_0 = 1$, $C_{k+1} = \sum_{i=0}^{k} C_i\, C_{k-i}$).
