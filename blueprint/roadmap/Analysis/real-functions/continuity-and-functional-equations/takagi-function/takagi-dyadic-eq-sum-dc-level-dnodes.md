# Takagi values at dyadic rationals from level $D$-node counts

Let $k$ and $r$ be
natural numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value
of the dyadic presentation $r/2^k$, write $n_i = \lfloor n/2^i \rfloor \bmod 2$ for the binary
digit of $n$ at position $i$, and let $\lambda_i(n)$ be the level-$i$ $D$-node count, which
equals $n \bmod 2^i$ if $n_i = 0$ and $2^i - (n \bmod 2^i)$ if $n_i = 1$. Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} \lambda_i(n)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} (n_i 2^i + (-1)^{n_i} (n \bmod 2^i)).$$

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 25 (`jis-2024-24.2.7-thm-25`).
