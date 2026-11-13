# Cycle-counting excedance generating function of s-fixed-points permutations

Let $R$ be a
commutative $\mathbb{Q}$-algebra, $x, q \in R$ and $s$ a natural number. Call a permutation
$\sigma$ of $\{0, \dots, n-1\}$ an $s$-fixed-points permutation if every fixed point of $\sigma$
is less than $s$ and any two points less than $s$ in the same cycle of $\sigma$ are equal. Write
$e(\sigma)$ for the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ for the number of cycles
of $\sigma$, fixed points included. Let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)}
u^n/n!$ over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and let
$F(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$ over the
$s$-fixed-points permutations $\sigma$ of $\{0, \dots, n-1\}$. Then for every formal power series
$L$ in $u$ over $R$ with zero constant term and $\exp(L) = A(x,u)$,

$$\frac{d^s}{du^s} F(q,x,u) = q^s \left(A(x,u) \exp((x-1)u)\right)^s \exp(qL) \exp(-qu).$$

Here $\exp(qL)$ is the paper's $(A(x,u))^q$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Theorem 59 (`jis-2025-25.5.7-thm-59`).
