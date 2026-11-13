# Recurrence for permutations with cycle lengths at most r, by excedances

Let $r \ge 2$.
An excedance of a permutation $\sigma$ is an $i$ with $\sigma(i) > i$. Let $A^{r-}_{n,m}$ be the
number of permutations of $\{1, \dots, n\}$ all of whose cycles have length at most $r$ and which
have exactly $m$ excedances, and let $C_{\ell,i}$ be the number of circular permutations of
$\ell$ objects (permutations with a single cycle through all points) with exactly $i$
excedances. Then for all natural numbers $m \le n$,

$$A^{r-}_{n+1,m} = \sum_{j=1}^{r-1} \binom{n}{j} \sum_{i=0}^{m} C_{j+1,i}\, A^{r-}_{n-j,m-i} +
A^{r-}_{n,m}.$$

A term with $j > n$ vanishes because $\binom{n}{j} = 0$; there $n - j$ is read as $0$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 10 (`jis-2025-25.5.7-thm-10`).
