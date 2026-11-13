# Permutations avoiding a prescribed set of cycle lengths

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $\mathcal{R}$ be a finite set of integers, each at
least $2$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices $i$
with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included; for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects; and let $A(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$,
summed over all permutations $\sigma$ of $n$ objects. Then in $R[[u]]$
$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! =
A(q,x,u) \exp\big(-q x \sum_{r \in \mathcal{R}} A_{r-1}(x)\,u^r/r!\big)$, where the inner sum on
the left runs over the permutations $\sigma$ of $n$ objects none of whose cycles has length in
$\mathcal{R}$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 67 (`jis-2025-25.5.7-cor-67`).
