# Derivative formula for prescribed cycle lengths through the first $s$ points, with $k$ cycles

**Derivative formula for prescribed cycle lengths through the first $s$ points, with $k$
cycles.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, $s \le k$ natural numbers
and $r : \mathbb{N} \to \mathbb{N}$ with $r(i) \ge 2$ for all $i < s$. For a permutation $\sigma$
of $\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$
the number of cycles of $\sigma$, fixed points included, and for $m \ge 0$ let
$A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of $\{0, \dots, m-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F_k(x,u)$ be the same series with
the inner sum restricted to the $\sigma$ with $c(\sigma) = k$ in which no two distinct points
less than $s$ lie in the same cycle and each point $i < s$ lies in a cycle of length $r(i)$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(G) = \sum_{m \ge 0} G^m/m!$, then the $s$-th derivative in $u$ is

$$\frac{d^s}{du^s} F_k(x,u) = x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) \frac{L^{k-s}}{(k-s)!}.$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 63 (`jis-2025-25.5.7-thm-63`).
