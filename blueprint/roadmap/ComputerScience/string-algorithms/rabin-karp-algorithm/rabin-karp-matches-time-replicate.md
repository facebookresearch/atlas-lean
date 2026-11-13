# Exact cost of Rabin–Karp matching on repeated-symbol words

Let $d$ be a base, $q > 0$ a
modulus, $a$ a natural number and $m$, $n$ natural numbers with $0 < m \le n$. Put
$t = \bigl(a \sum_{i\lt m} d^i\bigr) \bmod q$, and let $\beta = 1$ if
$t < (a \cdot (d^{m-1} \bmod q)) \bmod q$ and $\beta = 0$ otherwise. Then Rabin–Karp matching
with base $d$ and modulus $q$ of the pattern $a^m$ in the text $a^n$ (the lists of $m$ and of
$n$ copies of $a$) has counted cost exactly

$$(8m - 1) + (n - m + 1) + 7(n - m) + (n - m)\beta + m(n - m + 1).$$

The last term is $m$ symbol comparisons at each of the $n - m + 1$ alignments.
