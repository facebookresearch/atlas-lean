# Staver's identity for alternating reciprocal binomial sums

For a natural number $n$,
let $S_0(n) = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k}^{-1}$ and
$S_1(n) = \sum_{k=0}^{n} (-1)^{n-k} \, k \binom{n}{k}^{-1}$, computed in $\mathbb{Q}$.
If $n$ is even, then $S_1(n) = \frac{n}{2} S_0(n)$; if $n$ is odd, then $S_0(n) = 0$.

Both parts follow by pairing $k$ with $n - k$: for odd $n$ the paired terms cancel, for even $n$ they average to $n/2$.

## Sources

- Renzo Sprugnoli, *Alternating Weighted Sums of Inverses of Binomial Coefficients*, J. Integer Seq. 15 (2012), Article 12.6.3, Theorem 1 (Staver's identity) and its proof, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Sprugnoli/sprugnoli6.tex>.
