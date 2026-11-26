# Ballot numbers

For natural numbers $n$ and $k$, the ballot number $B(n, k)$ is the
integer part of $\max(n + 1 - k, 0) \binom{n+k}{n} / (n + 1)$. For $k \le n + 1$ the division
is exact, so $B(n, k) = \frac{n - k + 1}{n + 1} \binom{n+k}{n}$ (OEIS A009766), and
$B(n, k) = 0$ for $k > n + 1$.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1.
