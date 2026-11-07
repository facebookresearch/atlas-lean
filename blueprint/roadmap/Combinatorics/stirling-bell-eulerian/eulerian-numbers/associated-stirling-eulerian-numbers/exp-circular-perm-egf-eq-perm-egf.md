# Logarithm of the Eulerian generating function

Let $R$ be a commutative $\mathbb{Q}$-algebra
and $x \in R$, and work with formal power series in $u$ over $R$. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (points $i$ with $\sigma(i) > i$), and let $S_n$ be the
set of permutations of $\{0, \dots, n-1\}$. Let
$A(x,u) = \sum_{n \ge 0} \sum_{\sigma \in S_n} x^{e(\sigma)} u^n/n!$ be the exponential generating
function of excedances over all permutations, and let $C(x,u)$ be the same sum restricted to
circular permutations, that is, to the permutations of $n \ge 1$ points that consist of a single
cycle. Then $\exp C(x,u) = A(x,u)$, that is, $C(x,u) = \ln A(x,u)$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 6 (`jis-2025-25.5.7-thm-6`).
