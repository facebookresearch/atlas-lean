# Excedance generating function of permutations with all cycles longer than $r$

Let $R$
be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 1$. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be the number of points $i$ with
$\sigma(i) > i$, let $A_n(x) = \sum_{\sigma} x^{\operatorname{exc}(\sigma)}$, summed over all
permutations of $\{0, \dots, n-1\}$, and let $A(x,u) = \sum_{n \ge 0} A_n(x) u^n/n!$. Let
$A^r(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{\operatorname{exc}(\sigma)} u^n/n!$, the inner sum
over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles (fixed points counted
as cycles of length one) have length greater than $r$. Then, as formal power series in $u$
over $R$,

$$A^r(x,u) = A(x,u) \exp\left(-u - x \sum_{j=1}^{r-1} \frac{A_j(x)\, u^{j+1}}{(j+1)!}\right).$$

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 32 (`jis-2025-25.5.7-thm-32`).
