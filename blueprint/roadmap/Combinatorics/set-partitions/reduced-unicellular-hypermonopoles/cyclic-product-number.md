# Cyclic product numbers

For natural numbers $n$ and $k$, write $c(m, j)$ for the unsigned
Stirling numbers of the first kind. The cyclic product number $H(n, k)$ is the quotient
$c(n + 1, k) / \binom{n + 1}{2}$, rounded down to a natural number, when $n + k$ is even
(equivalently, $n - k$ is even), and $0$ when $n + k$ is odd. Division by zero gives $0$, so
$H(0, k) = 0$ for every $k$.

These are the numbers displayed in Theorem 5 of the source. The numbers $H(n + 1, k)$ are the
Hultman numbers (OEIS A164652).

## Sources

- Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Theorem 5.
