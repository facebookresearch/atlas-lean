# Recurrence for central binomial sums with harmonic numbers of even index

For a natural
number $n$, let $H_m = \sum_{i=1}^{m} 1/i$ be the harmonic numbers, $c_n = \binom{2n}{n}/4^n$,
and for natural $r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^{2H}(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r H_{2k}$, with $0^0 = 1$. Then

$$S_0^{2H}(n) = c_n \big((2n+1) H_{2n} - (4n+1)\big) + 1;$$

for every $r \ge 1$

$$(2r+1) S_r^{2H}(n) = n^r c_n \Big((2n+1) H_{2n} + n + \frac{3}{2}\Big) + (-1)^r -
\frac{3}{2} S_r(n) + 2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^{2H}(n) -
\sum_{j=0}^{r} \binom{r+1}{j} (-1)^{r-j} S_j(n);$$

and

$$S_1^{2H}(n) = \frac{1}{9} c_n \big(3n(2n+1) H_{2n} - 4n^2 + 7n + 3\big) - \frac{1}{3}.$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Theorem 3.
