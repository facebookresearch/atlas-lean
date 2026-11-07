# The $q$-analogue for cycles longer than $r$ is a $q$-th power

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$ and $r$ a natural number. For a permutation $\sigma$ of
$\{0, \dots, n-1\}$ let $\operatorname{exc}(\sigma)$ be the number of points $i$ with
$\sigma(i) > i$ and $\operatorname{cyc}(\sigma)$ its number of cycles (fixed points counted as
cycles of length one). Let

$$A^r(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!}
\sum_{\sigma} x^{\operatorname{exc}(\sigma)} q^{\operatorname{cyc}(\sigma)},$$

the inner sum over the permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles have
length greater than $r$, and let $A^r(x,u) = A^r(1,x,u)$. If $L$ is a formal power series in
$u$ over $R$ with $L(0) = 0$ and $\exp L = A^r(x,u)$, then $A^r(q,x,u) = \exp(qL)$.

This is the paper's $A^r(q,x,u) = (A^r(x,u))^q$, with the power read through the logarithm $L$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 35 (`jis-2025-25.5.7-thm-35`).
