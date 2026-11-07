# Alternating reciprocal central binomial sum with $O_n - O_k$

Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$ and $r$
(with $0^0 = 1$),

$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \frac{4^k}{\binom{2k}{k}} k^r (O_n - O_k) =
\frac{1}{\binom{2n}{n}} \sum_{k=0}^{\min(r,\, n-1)} \frac{(-1)^k}{2(n-k)-1}\, k! {r \brace k}
4^k \binom{2(n-k)}{n-k} (1 - O_{n-k-1}),$$

where the right-hand sum is empty when $n = 0$.

The paper's right-hand sum runs over all $k \le r$; its term $k = n$ vanishes there because
$1 - O_{-1} = 0$, so it is dropped here.

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Proposition 7 (`integers-2026-A109-prop-7`).
