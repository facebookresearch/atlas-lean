# Takagi values at dyadic rationals from binary digits

Let $k$ and $r$ be natural
numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value of the
dyadic presentation $r/2^k$, write $n_j = \lfloor n/2^j \rfloor \bmod 2$ for the binary digit of
$n$ at position $j$, and write $s_1(m)$ for the number of ones in the binary expansion of $m$.
Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 \sum_{j=i}^{k} n_j + 4)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 s_1(\lfloor n/2^i \rfloor) + 4).$$

The paper prints the inner sum as $\sum_{j=i}^{k} n_i$; it is read here as $\sum_{j=i}^{k} n_j$.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 27 (`jis-2024-24.2.7-thm-27`).
