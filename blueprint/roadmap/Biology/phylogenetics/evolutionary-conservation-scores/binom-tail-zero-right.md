# Binom Tail zero right

For $n, k \in \mathbb{N}$ and $p \in \mathbb{R}$, write

$$B(n, k, p) = \sum_{i = k}^{n} \binom{n}{i} p^i (1 - p)^{n - i}$$

for this polynomial, defined for every real $p$ (with $0^0 = 1$). When $0 \le p \le 1$ it is the upper tail probability $P(X \ge k)$ of $X \sim \mathrm{Bin}(n, p)$; for other $p$ it need not be a probability (for $n = k = 1$ it equals $p$). If $k \ge 1$, then $B(n, k, 0) = 0$.
