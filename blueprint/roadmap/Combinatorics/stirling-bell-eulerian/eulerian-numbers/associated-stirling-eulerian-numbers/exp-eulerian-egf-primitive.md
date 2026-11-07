# Primitive of the Eulerian generating function

Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x \in R$, and work with formal power series in $u$ over $R$. For a
permutation $\sigma$ write $e(\sigma)$ for its number of excedances (points $i$ with
$\sigma(i) > i$), let $S_n$ be the set of permutations of $\{0, \dots, n-1\}$, and let
$A(x,u) = \sum_{n \ge 0} \sum_{\sigma \in S_n} x^{e(\sigma)} u^n/n!$. If $P(u)$ is a formal power
series in $u$ over $R$ with zero constant term whose derivative is $A(x,u)$, then
$\exp\bigl(x P(u) - (x-1)u\bigr) = A(x,u)$.

This is the paper's $P(x,u) = (\ln A(x,u) + u(x-1))/x$ with the division by $x$ cleared and the
logarithm exponentiated.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 13 (`jis-2025-25.5.7-cor-13`).
