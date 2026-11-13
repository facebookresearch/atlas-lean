# Excedance generating function of involutions

Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x, q \in R$. For a permutation $\sigma$ write $e(\sigma)$ for the number
of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for its number of cycles, fixed points included.
Summing over the involutions $\sigma$ of $\{0, \dots, n-1\}$ (permutations all of whose cycles
have length at most $2$), the following identity of formal power series in $u$ over $R$ holds:

$$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} \frac{u^n}{n!} = \exp(q(u + x u^2/2)).$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 39 (`jis-2025-25.5.7-cor-39`).
