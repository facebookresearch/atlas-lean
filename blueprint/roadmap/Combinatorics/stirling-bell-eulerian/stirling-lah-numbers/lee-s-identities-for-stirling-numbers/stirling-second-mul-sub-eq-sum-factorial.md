# Lee's identity for Stirling numbers of the second kind from higher columns

Write
$S(n, k)$ for the Stirling number of the second kind, the number of partitions of an $n$-element
set into $k$ nonempty blocks. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$,
the following identity of integers holds:

$$(n - k)\, S(n, k) = \sum_{j=2}^{n-k+1} (j-2)!\, (-1)^j \binom{k+j-1}{j}\, S(n, k+j-1).$$

This is Lee's Theorem 8 with the denominator $n - k$ cleared and the generalized binomial
coefficient written as $\binom{-k}{j} = (-1)^j \binom{k+j-1}{j}$.

## Sources

- Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 8.
