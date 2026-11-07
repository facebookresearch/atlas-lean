# Multifold partition diamonds with given fold and link sums

Let $d_1, \dots, d_M$ be
natural numbers, let $L_k = \sum_{m=1}^{k} (d_m + 1)$ for $0 \le k \le M$ be the link
positions, let $c = L_M + 1$, and let $i$ and $j$ be natural numbers. A function
$b : \mathbb{N} \to \mathbb{N}$ is a multifold partition diamond with fold sum $i$ and link sum
$j$ when the following hold: for every $k$ with $0 \le k < M$ and every $f$ with
$1 \le f \le d_{k+1}$, we have $b(L_k) \le b(L_k + f) \le b(L_{k+1})$; the sum of $b(p)$ over
the positions $p < c$ different from $L_0, \dots, L_M$ is $i$; and
$b(L_0) + \dots + b(L_M) = j$.

This models the paper's $P$-partitions (order-preserving maps to $\mathbb{Z}_{\ge 0}$) of the
poset in which, for each $k < M$, the folds at positions $L_k + 1, \dots, L_k + d_{k+1}$ lie
above the link at $L_k$ and below the link at $L_{k+1}$. In particular, when every
$d_k \ge 1$, $b(0)$ is the smallest of $b(0), \dots, b(c - 1)$.

## Sources

- Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds Revisited*, INTEGERS 26 (2026), Article A13, Sections 2-3.
