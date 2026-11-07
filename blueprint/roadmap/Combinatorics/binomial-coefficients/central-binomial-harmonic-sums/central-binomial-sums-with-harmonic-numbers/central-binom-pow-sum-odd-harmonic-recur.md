# Recurrence for central binomial sums with odd harmonic numbers

For a natural number $n$,
let $O_m = \sum_{i=1}^{m} 1/(2i-1)$ be the odd harmonic numbers, $c_n = \binom{2n}{n}/4^n$, and
for natural $r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^O(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r O_k$, with $0^0 = 1$. Then

$$S_0^O(n) = c_n \big((2n+1) O_n - 2n\big),$$

and for every $r \ge 1$

$$(2r+1) S_r^O(n) = n^r c_n \big((2n+1) O_n + 1\big) - S_r(n) +
2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^O(n).$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Theorem 1 (`integers-2026-A109-thm-1`).
