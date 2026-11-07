# Derivative formula for permutations with cycle lengths at most $r$ and separated first points

**Derivative formula for permutations with cycle lengths at most $r$ and separated first
points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s$ be natural
numbers with $r \ge 1$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for
its number of excedances (indices $i$ with $\sigma(i) > i$), and let
$A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Say that the first $s$ points of $\sigma$ are
separated when the points $i < \min(s, n)$ lie in pairwise distinct cycles. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let $F(u)$ be the same series with the inner sum restricted to those
$\sigma$ whose first $s$ points are separated. Then the $s$-th derivative of $F$ with respect to
$u$ is

$$F^{(s)}(u) = \left(1 + x \sum_{i=1}^{r-1} \frac{A_i(x)\, u^i}{i!}\right)^s A^{r-}(x,u).$$

The paper states $r \ge 2$; the case $r = 1$ also holds (both sides are $\exp(u)$), while for
$r = 0$ and $s = 1$ the identity fails (the left side is $0$, the right side $1$).

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 17 (`jis-2025-25.5.7-thm-17`).
