# Upward crossing counts of horizontal neighbours sum to an even number

Let $n \ge 1$ and let $d = (d_0, \dots, d_{n-1})$ be a cyclic sequence of directions $d_i \in \mathbb{Z}/4\mathbb{Z}$, indices taken modulo $n$. Direction $k$ is the unit step $s(k)$, with $s(0) = (1, 0)$ (east), $s(1) = (0, 1)$ (north), $s(2) = (-1, 0)$ (west), $s(3) = (0, -1)$ (south), and the walk with step directions $d$ has vertices $p_k = \sum_{0 \le i < k} s(d_i)$ for $k = 0, \dots, n-1$ (so $p_0 = 0$; vertex indices are also taken modulo $n$). For integers $a, b$ let $U(a, b)$ be the number of horizontal steps $k$ with $\min(x(p_k), x(p_{k+1})) = a$ and $y(p_k) > b$. Suppose the walk is closed, $\sum_{i} s(d_i) = 0$, and no vertical step $k$ with $x(p_k) = a + 1$ satisfies $\min(y(p_k), y(p_{k+1})) \le b < \max(y(p_k), y(p_{k+1}))$. Then

$$U(a, b) + U(a + 1, b) = 2\,N,$$

where $N$ is the number of indices $k$ such that $p_{k+1}$ lies on the half-line $\{(a+1, y) : y \ge b + 1\}$ and $p_k$ does not.
