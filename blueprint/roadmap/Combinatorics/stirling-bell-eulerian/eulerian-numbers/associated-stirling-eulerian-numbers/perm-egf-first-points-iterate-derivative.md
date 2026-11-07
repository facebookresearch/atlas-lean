# Derivative formula for permutations whose first $s$ points lie in distinct cycles

Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $s \in \mathbb{N}$. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $A_{[s]}(x,u)$ be the same series
with the inner sum restricted to the $\sigma$ in which no two distinct points less than $s$ lie
in the same cycle. Then the $s$-th derivative in $u$ is

$$\frac{d^s}{du^s} A_{[s]}(x,u) = \bigl(A(x,u) \exp((x-1)u)\bigr)^s A(x,u),$$

where $\exp(F) = \sum_{m \ge 0} F^m/m!$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 45 (`jis-2025-25.5.7-cor-45`).
