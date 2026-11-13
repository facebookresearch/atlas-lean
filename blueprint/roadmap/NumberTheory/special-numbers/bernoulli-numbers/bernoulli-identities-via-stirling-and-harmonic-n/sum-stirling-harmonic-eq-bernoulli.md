# Bernoulli numbers from Stirling and harmonic numbers

Let $j < n$ be natural numbers. Write
${n \brace k}$ for the Stirling numbers of the second kind, ${k \brack j}$ for the unsigned
Stirling numbers of the first kind (the number of permutations of $k$ elements with exactly $j$
cycles), $H_k = \sum_{i=1}^{k} 1/i$ for the harmonic numbers (so $H_0 = 0$), and $B_m$ for the
Bernoulli numbers, normalized so that $B_1 = -1/2$. Then, in the rational numbers,

$$
\sum_{k=j}^{n} (-1)^{k-j} {n \brace k} {k \brack j} H_k
= \left(\binom{n}{j} - 1\right) \frac{B_{n-j}}{n-j}.
$$

The paper also covers the diagonal case $n = j$, reading the right-hand side as a limit (both
sides are then $H_j$); that case is not included here.

## Sources

- Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Theorem 1, equation (5).
