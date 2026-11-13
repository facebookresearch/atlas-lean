# Permutations with $k$ cycles, all of length greater than $r$, by excedances

Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r, k \in \mathbb{N}$. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and
$c(\sigma)$ the number of cycles of $\sigma$, fixed points included. Let
$A^r(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points
included, as cycles of length $1$) have length greater than $r$, and let $A^r_k(x,u)$ be the same
series with the inner sum further restricted to the $\sigma$ with $c(\sigma) = k$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A^r(x,u)$, where
$\exp(F) = \sum_{m \ge 0} F^m/m!$, then $A^r_k(x,u) = L^k/k!$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 34 (`jis-2025-25.5.7-thm-34`).
