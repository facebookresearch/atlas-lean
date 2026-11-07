# Lee's identity for Stirling numbers of the first kind from higher columns

Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:

$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{k+j-1}{j}\, c(n, k+j-1).$$

This is Lee's Theorem 14 with the denominator $n - k$ cleared.

## Sources

- Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 14 (TeX label `thm:dwfmc`).
