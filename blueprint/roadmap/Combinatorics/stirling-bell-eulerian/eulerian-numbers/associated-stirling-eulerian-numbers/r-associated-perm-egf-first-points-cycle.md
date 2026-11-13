# Iterated derivative for $k$ cycles longer than $r$ with $s$ points in distinct cycles

Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r$, $s$, $k$ be natural
numbers with $r \ge 1$ and $s \le k$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$\operatorname{exc}(\sigma)$ be the number of points $i$ with $\sigma(i) > i$, let
$A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all permutations of
$\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let $A^r(x,u)$ be the
series $\sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$ with the inner sum
over the permutations of $\{0, \dots, n-1\}$ all of whose cycles (fixed points counted as
cycles of length one) have length greater than $r$, and let $[A^r_k(x,u)]_s$ be the same
series with the inner sum further restricted to the permutations that have exactly $k$ cycles
and whose points among $0, \dots, s-1$ lie in pairwise distinct cycles. If $L$ is a formal
power series in $u$ over $R$ with $L(0) = 0$ and $\exp L = A^r(x,u)$, then the $s$-th formal
derivative in $u$ satisfies

$$\frac{\partial^s}{\partial u^s} [A^r_k(x,u)]_s =
x^s \left(A(x,u) - \sum_{n=0}^{r-1} \frac{A_n(x)\, u^n}{n!}\right)^s \frac{L^{k-s}}{(k-s)!}.$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 37 (`jis-2025-25.5.7-thm-37`).
