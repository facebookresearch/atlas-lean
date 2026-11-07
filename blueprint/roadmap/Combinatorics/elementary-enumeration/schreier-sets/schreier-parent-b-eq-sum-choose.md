# Binomial-sum formula for the parent sequence b

Let $b^{(s)}_{p,n}$ be the parent
sequence: $0$ for $n \le (p - 1)s$, $1$ for $(p - 1)s < n \le ps + 1$, and
$b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for $n \ge ps + 2$. For positive integers
$s$, $p$ and $n$,

$$b^{(s)}_{p,n} = \sum_{i=0}^{\lfloor (n - s(p-1) - 1)/(sp+1) \rfloor}
\binom{n - s(p-1) - 1 - spi}{i},$$

where the sum is empty when $n \le s(p - 1)$.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Proposition 1 (`integers-2026-A53-prop-1`).
