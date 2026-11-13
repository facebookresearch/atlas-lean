# Permutations with all cycle lengths in a prescribed set

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$, and let $\mathcal{R}$ be a finite set of integers, each at
least $2$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices $i$
with $\sigma(i) > i$) and $c(\sigma)$ its number of cycles, fixed points included, and for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects. Then in $R[[u]]$
$\sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n! =
\exp\big(q x \sum_{r \in \mathcal{R}} A_{r-1}(x)\,u^r/r!\big)$, where the inner sum on the left
runs over the permutations $\sigma$ of $n$ objects all of whose cycles, fixed points included,
have length in $\mathcal{R}$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 65 (`jis-2025-25.5.7-thm-65`).
