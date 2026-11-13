# Cycle lengths at most r: the q-analogue is a q-th power

Let $R$ be a commutative
$\mathbb{Q}$-algebra, let $x, q \in R$ and let $r \ge 2$. For a permutation $\sigma$ write
$e(\sigma)$ for its number of excedances (the $i$ with $\sigma(i) > i$) and $c(\sigma)$ for its
number of cycles, fixed points included, and for $t \in R$ let

$$F_t(u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} t^{c(\sigma)},$$

where the inner sum runs over the permutations $\sigma$ of $\{1, \dots, n\}$ all of whose cycles
have length at most $r$. If $L$ is a formal power series in $u$ over $R$ with constant term $0$
and $\exp(L) = F_1(u)$, then $F_q(u) = \exp(qL)$. This is the identity $F_q = F_1^{\,q}$ with the
power read as $\exp(q \ln F_1)$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 16 (`jis-2025-25.5.7-cor-16`).
