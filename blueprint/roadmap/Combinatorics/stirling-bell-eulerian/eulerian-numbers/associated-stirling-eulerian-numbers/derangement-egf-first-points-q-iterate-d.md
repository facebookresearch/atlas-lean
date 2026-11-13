# Derangements whose first $s$ points lie in distinct cycles

Let $R$ be a commutative
$\mathbb{Q}$-algebra, $x, q \in R$ and $s \ge 0$. For a permutation $\sigma$ let $e(\sigma)$ be
its number of excedances (indices $i$ with $\sigma(i) > i$) and $c(\sigma)$ its number of
cycles, fixed points included. Let $A(x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} u^n/n!$,
summed over all permutations $\sigma$ of $n$ objects, and let $L \in R[[u]]$ have constant term
$0$ and satisfy $\exp L = A(x,u)$. Let
$D_s(q,x,u) = \sum_{n \ge 0} \sum_{\sigma} x^{e(\sigma)} q^{c(\sigma)} u^n/n!$, the inner sum
over the derangements $\sigma$ of $n$ objects (permutations without fixed points) in which the
first $s$ points (all points, if $n < s$) lie in pairwise distinct cycles. Then the $s$-th
derivative of $D_s$ with respect to $u$ equals $q^s x^s (A(x,u) - 1)^s \exp\big(q\,(L - u)\big)$,
which is the paper's $q^s x^s (A(x,u) - 1)^s (A(x,u) e^{-u})^q$ with the power read through $L$.

## Sources

- Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28 (2025), Article 25.5.7, Corollary 51 (`jis-2025-25.5.7-cor-51`).
