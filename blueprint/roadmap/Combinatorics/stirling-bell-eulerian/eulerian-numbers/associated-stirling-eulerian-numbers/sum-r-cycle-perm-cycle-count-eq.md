# Excedance and cycle polynomial of permutations with k cycles, all of length r

Let $R$ be
a commutative ring, let $x, q \in R$, let $r \ge 2$ and let $n, k \ge 0$. For a permutation
$\pi$ write $e(\pi)$ for its number of excedances (the $i$ with $\pi(i) > i$) and $c(\pi)$ for
its number of cycles, fixed points included, and let $A_{r-1}(x) = \sum_{\sigma} x^{e(\sigma)}$,
summed over the permutations $\sigma$ of $\{1, \dots, r - 1\}$. Summing over the permutations
$\pi$ of $\{1, \dots, n\}$ that have exactly $k$ cycles, all of length exactly $r$,

$$\sum_{\pi} x^{e(\pi)} q^{c(\pi)} = \frac{(rk)!}{(r!)^k\, k!}\, x^k q^k A_{r-1}(x)^k$$

if $n = kr$, and the sum is $0$ otherwise.

The quotient $(rk)!/((r!)^k k!)$ is an exact natural-number division.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 24 (`jis-2025-25.5.7-cor-24`).
