# Lee's identity for Stirling numbers of the first kind from smaller rows

Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:

$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{n}{j}\, (j-2)!\, c(n-j+1, k).$$

This is Lee's Theorem 11 with the denominator $n - k$ cleared.

## Sources

- Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 11.
