# Every permutiple has a cycle-preserving digit permutation

Let $n$, $b$ and
$d_0, \dots, d_k$ be natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$ such
that $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple. Then there is a permutation
$\hat\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$ is also an
$(n, b, \hat\sigma)$-permutiple and the digits along each cycle of $\hat\sigma$ are distinct:
for all $j \in \{0, \dots, k\}$ and all $i \ge 0$, if $d_{\hat\sigma^i(j)} = d_j$ then
$\hat\sigma^i(j) = j$.

Unlike the paper, no assumption $1 < n < b$ is made.

## Sources

- B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025), Article A13, Theorem 5 (`integers-2025-A13-thm-5`), with Definition 5 (cycle-preserving permutations).
