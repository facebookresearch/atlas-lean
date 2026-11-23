# Recursive CUT-ROD

Let $\alpha$ be an additive commutative monoid with a linear order,
and let $p_1, \dots, p_n \in \alpha$ be prices, $p_i$ being the price of a piece of length $i$.
Recursive CUT-ROD returns $r(n)$, where $r(0) = 0$ and, for $1 \le j \le n$,
$r(j) = \max(p_1 + r(j - 1), p_2 + r(j - 2), \dots, p_j + r(0))$. The first cuts
$i = 1, \dots, j$ are scanned in increasing order and every $r(j - i)$ is recomputed by a fresh
recursive call, without memoization. One cost tick is charged at every invocation, including
the root call and every call on an empty rod.
