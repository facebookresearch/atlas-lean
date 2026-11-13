# Signed excedance–cycle sum over s-fixed-points permutations, cycle weight -s-1

Let
$s \le n$ be natural numbers. Call a permutation $\sigma$ of $\{0, \dots, n-1\}$ an
$s$-fixed-points permutation if every fixed point of $\sigma$ is less than $s$ and any two points
less than $s$ in the same cycle of $\sigma$ are equal. Write $e(\sigma)$ for the number of $i$
with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles of $\sigma$, fixed points included.
Then, summing over the $s$-fixed-points permutations $\sigma$ of $\{0, \dots, n-1\}$, the sum
$S = \sum_{\sigma} x^{e(\sigma)} (-s-1)^{c(\sigma)}$ in the polynomial ring $\mathbb{Z}[x]$
satisfies

$$(x - 1) S = (-1)^s (s+1)^s \left(x (s x + 1)^{n-s} - (s+1)^{n-s} x^{n-s}\right).$$

This is the paper's formula with the denominator $x - 1$ cleared.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 61 (`jis-2025-25.5.7-cor-61`).
