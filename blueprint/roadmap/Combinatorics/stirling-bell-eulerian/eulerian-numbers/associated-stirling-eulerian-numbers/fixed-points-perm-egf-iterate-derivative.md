# Excedance generating function of s-fixed-points permutations

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x \in R$ and $s$ a natural number. Call a permutation $\sigma$ of
$\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$ is less than
$s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write $e(\sigma)$
for the number of $i$ with $\sigma(i) > i$, let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma}
x^{e(\sigma)} u^n/n!$ over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(x,u)$ be
the same series restricted to the $s$-fixed-points permutations. Then, as formal power series in
$u$ over $R$,

$$\frac{d^s}{du^s} F(x,u) = \left(A(x,u) \exp((x-1)u)\right)^s A(x,u) \exp(-u).$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 57 (`jis-2025-25.5.7-thm-57`).
