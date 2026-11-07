# Excedance generating function of circular permutations of at most $r$ objects

Let
$R$ be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 1$. For a permutation $\sigma$
let $e(\sigma)$ be its number of excedances (indices $i$ with $\sigma(i) > i$), and for
$j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over all permutations $\sigma$ of
$j$ objects. Then in $R[[u]]$
$\sum_{n=1}^{r} \sum_{\sigma} x^{e(\sigma)} u^n/n! =
u + x \sum_{j=1}^{r-1} A_j(x)\,u^{j+1}/(j+1)!$, where the inner sum on the left runs over the
circular permutations $\sigma$ of $n$ objects (those with a single cycle through all $n$
points).

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 7 (`jis-2025-25.5.7-thm-7`).
