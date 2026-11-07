# Power-weighted binomial sums of a second-order linear recurrence

Let $a$ and $b$ be real
numbers and let $(W_n)_{n \ge 0}$ be a real sequence with $W_{n+2} = a W_{n+1} + b W_n$ for all
$n \ge 0$. Write $S(r, i)$ for the Stirling numbers of the second kind and
$(N)_i = N(N-1) \cdots (N-i+1)$ for the falling factorial, with $(N)_0 = 1$. Then for all natural
numbers $N$ and $r$, with the convention $0^0 = 1$,

$$\sum_{k=0}^{N} k^r \binom{N}{k} a^k b^{N-k} W_k = \sum_{i=0}^{r} S(r, i) (N)_i a^i W_{2N-i},$$

where the terms with $i > N$ vanish because $(N)_i = 0$.

## Sources

- Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5.
