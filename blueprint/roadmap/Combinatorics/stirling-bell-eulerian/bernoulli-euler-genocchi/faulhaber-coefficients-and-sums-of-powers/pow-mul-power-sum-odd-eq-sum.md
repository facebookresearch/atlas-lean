# Odd power sums in terms of $\binom{n+m}{2m-1}$

For natural numbers $k \ge 1$ and $n$,
write $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \dots + n^{2k-1}$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and let $Q_{k,1}(n) = n^{2k-1}$ and
$Q_{k,m}(n) = 2 \sum_{j=m}^{k} \binom{2k-1}{2j-2} R(j-1, m-1)\, n^{2k-2j+1}$ for $m \ge 2$. Then
$2^{2k-1} S_{2k-1}(n) = \sum_{m=1}^{k} Q_{k,m}(n) \binom{n+m}{2m-1}$.

## Sources

- José L. Cereceda, "Sums of Powers of Integers and the Sequence A304330", Theorem 10.
