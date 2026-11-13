# Excedance generating function of circular permutations of more than $r$ objects

Let $R$
be a commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 2$, and work with formal power series
in $u$ over $R$. For a permutation $\sigma$ let $e(\sigma)$ be its number of excedances (indices
$i$ with $\sigma(i) > i$). For $j \ge 0$ let $A_j(x) = \sum_{\sigma} x^{e(\sigma)}$, summed over
all permutations $\sigma$ of $j$ objects, and let $A(x,u) = \sum_{n \ge 0} A_n(x)\, u^n/n!$. Let
$C^{r+}(x,u) = \sum_{n \ge r+1} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, where the inner sum runs over
the circular permutations $\sigma$ of $n$ objects (those with a single cycle through all $n$
points). Then

$$\exp C^{r+}(x,u) =
A(x,u) \exp\Bigl(-u - x \sum_{i=1}^{r-1} A_i(x)\, \frac{u^{i+1}}{(i+1)!}\Bigr).$$

This is the identity
$C^{r+}(x,u) = \ln\bigl(A(x,u) \exp(-u - x \sum_{i=1}^{r-1} A_i(x)\, u^{i+1}/(i+1)!)\bigr)$
written in exponential form.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 9 (`jis-2025-25.5.7-thm-9`).
