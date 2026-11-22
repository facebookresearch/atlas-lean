# Bottom-up zero-one knapsack algorithm

Given knapsack items $x_0, \dots, x_{n-1}$ with
weights $w_i$ and values $v_i$ and a capacity $W \in \mathbb{N}$, the algorithm fills a table
$V(i, c)$ for $0 \le i \le n$ and $0 \le c \le W$ by $V(0, c) = 0$ and, for $i < n$,
$V(i + 1, c) = \max(V(i, c), V(i, c - w_i) + v_i)$ if $w_i \le c$ and $V(i + 1, c) = V(i, c)$
otherwise. Starting from $c = W$, it then inspects the rows $i = n, n - 1, \dots, 1$: if
$V(i, c) = V(i - 1, c)$ it skips item $i - 1$, and otherwise it selects index $i - 1$ and
replaces $c$ by $c - w_{i-1}$. It returns the selected index set together with the value
$V(n, W)$. Each of the $n(W + 1)$ cells of rows $1, \dots, n$ costs one tick, and each of the
$n$ inspected rows costs one tick.
