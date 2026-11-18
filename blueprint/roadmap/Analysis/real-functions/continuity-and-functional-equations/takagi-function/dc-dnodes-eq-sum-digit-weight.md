# Binary-digit formula for the divide-and-conquer D-node count

Let $\delta$ be the
divide-and-conquer D-node count and let $s_1(m)$ be the number of ones in the binary expansion
of $m$. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$ and let $n_j$ be the binary
digit of $n$ at $2^j$. Then

$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2 \sum_{j=i}^{k} n_j + 4\Big),$$

and also

$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2\, s_1(\lfloor n / 2^i \rfloor) + 4\Big).$$

The printed inner sum $\sum_{j=i}^k n_i$ is read as $\sum_{j=i}^k n_j$.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 22 (`jis-2024-24.2.7-thm-22`).
