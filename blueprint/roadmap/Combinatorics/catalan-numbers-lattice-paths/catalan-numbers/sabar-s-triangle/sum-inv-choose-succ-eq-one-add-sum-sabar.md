# Reciprocal binomial sums from Sabar's triangle

For every natural number $n \ge 2$, the
entries $s(n-1, i)$ of Sabar's triangle satisfy

$$\frac{1}{n+1} \sum_{i=0}^{n} \binom{n}{i}^{-1} =
1 + \sum_{i=0}^{n-2} \frac{(-1)^{n-i-1} \, s(n-1, i)}{(n-i)(n+1-i)}.$$

This is the source's Corollary 1 with the sign used in its proof. As printed, with $(-1)^{n-i}$,
it fails at $n = 2$: the left side is $5/6$ but $1 + s(1, 0)/(2 \cdot 3) = 7/6$.

## Sources

- Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27, Corollary 1.
