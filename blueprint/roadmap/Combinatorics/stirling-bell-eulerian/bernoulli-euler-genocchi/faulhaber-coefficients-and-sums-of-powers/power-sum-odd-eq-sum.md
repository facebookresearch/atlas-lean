# Knuth's binomial formula for the odd power sums

For all natural numbers $k \ge 1$ and
$n$, the power sum $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \cdots + n^{2k-1}$ satisfies

$$S_{2k-1}(n) = \sum_{m=1}^{k} R(k, m) \cdot \frac{1}{m} \binom{n + m}{2m},$$

where $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$ is the array of OEIS A304330.

## Sources

- José L. Cereceda, "Sums of Powers of Integers and the Sequence A304330", Proposition 3.
