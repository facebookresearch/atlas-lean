# Derivative formula for permutations with $k$ cycles whose first $s$ points lie in distinct cycles

**Derivative formula for permutations with $k$ cycles whose first $s$ points lie in distinct
cycles.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $s \le k$ natural numbers.
For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with
$\sigma(i) > i$ and $c(\sigma)$ the number of cycles of $\sigma$, fixed points included. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $A_{[s],k}(x,u)$ be the same
series with the inner sum restricted to the $\sigma$ with $c(\sigma) = k$ in which no two
distinct points less than $s$ lie in the same cycle. If $L \in R[[u]]$ has zero constant term
and $\exp(L) = A(x,u)$, where $\exp(F) = \sum_{m \ge 0} F^m/m!$, then the $s$-th derivative in
$u$ is

$$\frac{d^s}{du^s} A_{[s],k}(x,u) =
\bigl(A(x,u) \exp((x-1)u)\bigr)^s \frac{L^{k-s}}{(k-s)!}.$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 46 (`jis-2025-25.5.7-cor-46`).
