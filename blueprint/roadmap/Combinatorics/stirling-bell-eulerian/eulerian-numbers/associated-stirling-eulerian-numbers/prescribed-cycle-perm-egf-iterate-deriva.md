# Derivative formula for prescribed cycle lengths through the first $s$ points

Let $R$ be
a commutative $\mathbb{Q}$-algebra, $x \in R$, $s \in \mathbb{N}$ and
$r : \mathbb{N} \to \mathbb{N}$ with $r(i) \ge 2$ for all $i < s$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $e(\sigma)$ be the number of $i$ with $\sigma(i) > i$, and for $m \ge 0$
let $A_m(x) = \sum_{\sigma} x^{e(\sigma)}$ over all permutations $\sigma$ of
$\{0, \dots, m-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} \in R[[u]]$, the inner sum
over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(x,u)$ be the same series with
the inner sum restricted to the $\sigma$ in which no two distinct points less than $s$ lie in
the same cycle and each point $i < s$ lies in a cycle of length $r(i)$. Then the $s$-th
derivative in $u$ is

$$\frac{d^s}{du^s} F(x,u) = x^s \Bigl(\prod_{i=0}^{s-1}
\frac{A_{r(i)-1}(x)\, u^{r(i)-1}}{(r(i)-1)!}\Bigr) A(x,u).$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 62 (`jis-2025-25.5.7-thm-62`).
