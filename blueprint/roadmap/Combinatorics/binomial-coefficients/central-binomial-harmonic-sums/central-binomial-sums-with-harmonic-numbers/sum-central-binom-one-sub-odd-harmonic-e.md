# Central binomial sums weighted by $1 - O_{k-1}$, in r-Stirling form

Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${a \brace b}_c$ denote the r-Stirling numbers of the second kind. For all natural numbers $n$ and
$r$,

$$\sum_{k=1}^{n} \frac{k^r \binom{2k}{k}}{4^k (2k-1)} (1 - O_{k-1}) =
\frac{\binom{2n}{n}}{4^n} \sum_{k=0}^{\min(r,n)} (-1)^k k! {r+n-k \brace n}_{n-k}
\binom{n}{k} \frac{4^k}{\binom{2k}{k}} (O_n - O_k),$$

and in particular

$$\sum_{k=1}^{n} \frac{\binom{2k}{k}}{4^k (2k-1)} (1 - O_{k-1}) = \frac{\binom{2n}{n}}{4^n} O_n.$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Proposition 3.
