# Derivative formula for $r$-cycle permutations with separated first points

Let $R$ be
a commutative $\mathbb{Q}$-algebra, $x \in R$, and let $r, s$ be natural numbers with $r \ge 2$.
For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances
(indices $i$ with $\sigma(i) > i$), and let $A_j(x) = \sum_{\sigma \in S_j} x^{e(\sigma)}$. Call
$\sigma$ an $r$-cycle permutation when every cycle of $\sigma$, fixed points included, has exactly
$r$ elements, and say that its first $s$ points are separated when the points $i < \min(s, n)$
lie in pairwise distinct cycles. Let
$A^{(r)}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n! \in R[[u]]$, the inner sum over
the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$, and let $F(u)$ be the same series
with the inner sum restricted to those $\sigma$ whose first $s$ points are separated. Then the
$s$-th derivative of $F$ with respect to $u$ is

$$F^{(s)}(u) = x^s \left(\frac{A_{r-1}(x)\, u^{r-1}}{(r-1)!}\right)^s A^{(r)}(x,u).$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 27 (`jis-2025-25.5.7-thm-27`).
