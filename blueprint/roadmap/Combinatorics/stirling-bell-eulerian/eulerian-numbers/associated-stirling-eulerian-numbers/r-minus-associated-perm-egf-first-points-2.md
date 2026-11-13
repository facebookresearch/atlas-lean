# Derivative formula for permutations with cycle lengths at most $r$, $k$ cycles and separated first points

**Derivative formula for permutations with cycle lengths at most $r$, $k$ cycles and
separated first points.** Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let
$r, s, k$ be natural numbers with $r \ge 1$ and $s \le k$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances (indices $i$ with
$\sigma(i) > i$) and $c(\sigma)$ for its number of cycles, fixed points included, and let
$A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Say that the first $s$ points of $\sigma$ are
separated when the points $i < \min(s, n)$ lie in pairwise distinct cycles. Let
$A^{r-}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points included, have
at most $r$ elements, and let $F(u)$ be the same series with the inner sum restricted to those
$\sigma$ with $c(\sigma) = k$ whose first $s$ points are separated. If $L \in R[[u]]$ has zero
constant term and $\exp(L) = A^{r-}(x,u)$, where $\exp$ of a series with zero constant term is
its substitution into the exponential series, then the $s$-th derivative of $F$ with respect to
$u$ is

$$F^{(s)}(u) = \Big(1 + x \sum_{i=1}^{r-1} \frac{A_i(x)\, u^i}{i!}\Big)^s \frac{L^{k-s}}{(k-s)!}.$$

The hypothesis $r \ge 1$ is needed: for $r = 0$ and $s = k = 1$ the left side is $0$ and the
right side is $1$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 18 (`jis-2025-25.5.7-thm-18`).
