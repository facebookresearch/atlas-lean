# Expected fraction of set bits in a Bloom filter

Let $m, n, k \in \mathbb{N}$ with $m > 0$. The average, over all maps $H$ from
$\{0, \dots, n - 1\} \times \{0, \dots, k - 1\}$ to $\{0, \dots, m - 1\}$, of the fraction of the
$m$ bits set by $H$ equals $1 - (1 - 1/m)^{n k}$.
