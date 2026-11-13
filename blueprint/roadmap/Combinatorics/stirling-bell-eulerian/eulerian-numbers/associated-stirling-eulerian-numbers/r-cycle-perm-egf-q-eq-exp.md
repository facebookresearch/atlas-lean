# Cycle-weighted exponential formula for $r$-cycle permutations

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $r \ge 2$ be a natural number. For a permutation
$\sigma$ of $\{0, \dots, n-1\}$ write $e(\sigma)$ for its number of excedances (indices $i$ with
$\sigma(i) > i$) and $c(\sigma)$ for its number of cycles, fixed points included, and let
$A_{r-1}(x) = \sum_{\sigma \in S_{r-1}} x^{e(\sigma)}$. Call $\sigma$ an $r$-cycle permutation
when every cycle of $\sigma$, fixed points included, has exactly $r$ elements, and let
$A^{(r)}(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! \in R[[u]]$,
the inner sum over the $r$-cycle permutations $\sigma$ of $\{0, \dots, n-1\}$. Then

$$A^{(r)}(q,x,u) = \exp\left(\frac{q\, x\, A_{r-1}(x)\, u^r}{r!}\right),$$

where $\exp$ of a series with zero constant term is its substitution into the exponential series.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 23 (`jis-2025-25.5.7-thm-23`).
