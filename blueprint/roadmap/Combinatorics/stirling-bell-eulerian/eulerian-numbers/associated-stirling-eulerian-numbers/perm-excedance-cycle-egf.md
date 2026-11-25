# Excedance and cycle generating function of a permutation family

Let $R$ be a
commutative $\mathbb{Q}$-algebra, let $x, q \in R$, and for each $n$ let $P_n$ be a set of
permutations of $\{0, 1, \dots, n-1\}$. The excedance and cycle exponential generating function
of the family $(P_n)$ is the formal power series in $u$ over $R$

$$\sum_{n \ge 0} \frac{1}{n!} \Big(\sum_{\sigma \in P_n} x^{e(\sigma)} q^{c(\sigma)}\Big) u^n,$$

where $e(\sigma)$ is the number of excedances of $\sigma$ (points $i$ with $\sigma(i) > i$) and
$c(\sigma)$ its number of cycles, fixed points counted as cycles of length one.

With $q = 1$ this is the paper's $P(x, u)$, and for general $q$ its $q$-analogue $P(q, x, u)$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 6 and Corollary 43 (the series `C(x,u)` and `A_k(x,u)`), Corollary 24 (the weight `x^{e(π)} q^{c(π)}`).
