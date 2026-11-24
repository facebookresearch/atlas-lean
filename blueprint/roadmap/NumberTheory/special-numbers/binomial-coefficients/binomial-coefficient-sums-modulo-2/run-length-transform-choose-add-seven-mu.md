# Sum of $\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2$ as a run length transform

For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+7k}{3n+k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the shifted Padovan sequence $P$, given by
$P(0) = 1$, $P(1) = 0$, $P(2) = 1$ and $P(i + 3) = P(i + 1) + P(i)$, that is,
$1, 0, 1, 1, 1, 2, 2, 3, \dots$ (the Padovan numbers, OEIS A000931, from offset $3$).

## Sources

- Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 13.
