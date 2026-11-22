# Recurrence for central binomial sums with harmonic numbers

For a natural number $n$,
let $H_m = \sum_{i=1}^{m} 1/i$ be the harmonic numbers, $c_n = \binom{2n}{n}/4^n$, and for natural
$r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^H(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r H_k$, with $0^0 = 1$. Then

$$S_0^H(n) = (2n+1)\, c_n (H_n - 2) + 2,$$

and for every $r \ge 1$

$$(2r+1) S_r^H(n) = n^r (2n+1)\, c_n (H_n + 1) + 2(-1)^r - S_r(n) +
2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^H(n) -
2 \sum_{j=0}^{r} \binom{r+1}{j} (-1)^{r-j} S_j(n).$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Theorem 2.
