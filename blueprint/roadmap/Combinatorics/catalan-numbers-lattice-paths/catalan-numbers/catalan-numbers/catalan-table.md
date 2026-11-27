# Bottom-up table of Catalan numbers

For a natural number $n$ let $T(n)$ be the list of natural numbers defined by $T(0) = [1]$ and, for $p = T(n)$, $T(n+1) = p$ followed by one more entry, the sum of the products of corresponding entries of $p$ and of its reverse (pairing entries up to the length of the shorter list). Writing $p = (p_0, \dots, p_m)$, the new entry is $\sum_{i=0}^{m} p_i\, p_{m-i}$, so $T(n)$ evaluates the Catalan recurrence $C_{n+1} = \sum_{i=0}^{n} C_i\, C_{n-i}$ bottom up.
