# Optimal BST table recurrence

Let $R$ be a linearly ordered additive commutative monoid
in which addition is monotone, let $n$ be a natural number, let
$p_0, \dots, p_{n-1}, q_0, \dots, q_n \in R$, and let $e$ and $\rho$ be the cost table and the
root table returned by the optimal binary search tree procedure on these weights. For
$a \le b \le n$ write $w(a, b) = \sum_{i=a}^{b-1} p_i + \sum_{i=a}^{b} q_i$. Then
$e[a][a] = q_a$ for every $a \le n$, and for all $a < b \le n$ there is an $r$ with
$a \le r < b$ such that $\rho[a][b-1] = r$, $e[a][b] = e[a][r] + e[r+1][b] + w(a, b)$, and for
every $t$ with $a \le t < b$

$$e[a][b] \le e[a][t] + e[t+1][b] + w(a, b),$$

with strict inequality when $t < r$. So $e[a][b]$ is the minimum of
$e[a][t] + e[t+1][b] + w(a, b)$ over $a \le t < b$, and $r$ is the earliest $t$ attaining it.
