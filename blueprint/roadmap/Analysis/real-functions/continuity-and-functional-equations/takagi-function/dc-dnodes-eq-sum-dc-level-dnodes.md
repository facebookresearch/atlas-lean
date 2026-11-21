# Level-sum formula for the divide-and-conquer D-node count

Let $\delta$ be the
divide-and-conquer D-node count. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$,
let $\lambda_i(n)$ be the level-$i$ D-node count, and let $n_i$ be the binary digit of $n$ at
$2^i$. Then

$$\delta(n) = \sum_{i=0}^{k-1} \lambda_i(n),$$

and explicitly

$$\delta(n) = \sum_{i=0}^{k-1} \left(n_i 2^i + (-1)^{n_i} (n \bmod 2^i)\right).$$

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 11 (`jis-2024-24.2.7-thm-11`).
