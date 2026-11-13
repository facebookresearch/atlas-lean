# Logarithm of the generating function of permutations with long cycles

Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x \in R$ and $r \ge 0$ an integer, and work with formal power
series in $u$ over $R$. For a permutation $\sigma$ write $e(\sigma)$ for its number of excedances
(points $i$ with $\sigma(i) > i$). Let
$C^{r+}(x,u) = \sum_{n \ge r+1} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points that consist of a single cycle, and let
$A^{r}(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n!$, the inner sum over the
permutations of $n$ points all of whose cycles, fixed points included, have length greater than
$r$. Then $\exp C^{r+}(x,u) = A^{r}(x,u)$, that is, $C^{r+}(x,u) = \ln A^{r}(x,u)$.

At $r = 0$ every permutation has all cycle lengths greater than $0$, so $A^{0}(x,u)$ runs over
all permutations, $C^{0+}(x,u)$ over all circular permutations, and this is Theorem 6.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 33 (`jis-2025-25.5.7-cor-33`).
