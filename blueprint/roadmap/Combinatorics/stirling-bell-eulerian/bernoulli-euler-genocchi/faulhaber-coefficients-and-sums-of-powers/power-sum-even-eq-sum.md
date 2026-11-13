# Knuth's formula for even power sums

For natural numbers $k \ge 1$ and $n$, write
$S_{2k}(n) = 1^{2k} + 2^{2k} + \dots + n^{2k}$ and
$R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$S_{2k}(n) = \sum_{m=1}^{k} R(k, m)\, \frac{2n+1}{2m+1} \binom{n+m}{2m}$.

## Sources

- José L. Cereceda, "Sums of Powers of Integers and the Sequence A304330", Proposition 3.
