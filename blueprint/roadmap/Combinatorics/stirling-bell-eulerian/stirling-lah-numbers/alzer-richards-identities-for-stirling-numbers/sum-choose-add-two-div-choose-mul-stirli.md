# Alternating Stirling sums with $\binom{n+1}{k+2}$

Write $S(n, k)$ for the Stirling
numbers of the second kind and $B_n$ for the Bernoulli numbers, with $B_1 = -1/2$. Let
$n \ge 1$ be a natural number. Then for every natural number $r$ with $1 \le r \le n$,

$$
\sum_{k=0}^{n-1} (-1)^k \frac{\binom{n+1}{k+2}}{\binom{r+k}{k}} S(r+k, k) =
r B_{r-1} + (n + r) B_r,
$$

and

$$
\sum_{k=0}^{n-1} (-1)^k \frac{\binom{n+1}{k+2}}{\binom{n+1+k}{k}} S(n+1+k, k) =
(-1/2)^{n+1} (n+1)! + (n+1) B_n + (2n+1) B_{n+1}.
$$

## Sources

- Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 4, Equation (6).
