# Derivative formula for $r$-cycle permutations with $k$ cycles and separated first points

Let $R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s, k$ be natural numbers
with $r \ge 2$ and $s \le k$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$
for its number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its number of
cycles, fixed points included, and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Call
$\sigma$ an $r$-cycle permutation when every cycle of $\sigma$, fixed points included, has exactly
$r$ elements, and say that its first $s$ points are separated when the points $i < \min(s, n)$
lie in pairwise distinct cycles. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(u)$ be the same series
with the inner sum restricted to those $\sigma$ with $c(\sigma) = k$ whose first $s$ points are
separated. If $L \in R[[u]]$ has zero constant term and $\exp(L) = A^{(r)}(x,u)$, where $\exp$ of
a series with zero constant term is its substitution into the exponential series, then the
$s$-th derivative of $F$ with respect to $u$ is

$$F^{(s)}(u) = x^s \left(\frac{A_{r-1}(x)\, u^{r-1}}{(r-1)!}\right)^s \frac{L^{k-s}}{(k-s)!}.$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 28 (`jis-2025-25.5.7-thm-28`).
