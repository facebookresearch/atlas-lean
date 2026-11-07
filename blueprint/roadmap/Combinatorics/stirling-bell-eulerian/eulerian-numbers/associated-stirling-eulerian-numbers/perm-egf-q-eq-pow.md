# Brenti's excedance and cycle generating function

Let $R$ be a commutative
$\mathbb{Q}$-algebra and $x, q \in R$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ let
$e(\sigma)$ be the number of $i$ with $\sigma(i) > i$ and $c(\sigma)$ the number of cycles of
$\sigma$, fixed points included. Let
$A(q,x,u) = \sum_{n \ge 0} \frac{u^n}{n!} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} \in R[[u]]$,
the inner sum over all permutations $\sigma$ of $\{0, \dots, n-1\}$, and $A(x,u) = A(1,x,u)$. If
$L \in R[[u]]$ has zero constant term and $\exp(L) = A(x,u)$, where
$\exp(F) = \sum_{m \ge 0} F^m/m!$, then $A(q,x,u) = \exp(qL)$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 44 (`jis-2025-25.5.7-cor-44`).
