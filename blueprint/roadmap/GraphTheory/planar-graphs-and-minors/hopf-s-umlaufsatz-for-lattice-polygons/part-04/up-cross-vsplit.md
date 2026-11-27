# Upward crossings of vertically adjacent cells differ by separating steps

Let $n \ge 1$ and let $d = (d_0, \dots, d_{n-1})$ be a cyclic sequence of directions $d_i \in \mathbb{Z}/4\mathbb{Z}$, indices taken modulo $n$. Direction $k$ is the unit step $s(k)$, with $s(0) = (1, 0)$ (east), $s(1) = (0, 1)$ (north), $s(2) = (-1, 0)$ (west), $s(3) = (0, -1)$ (south), and the walk with step directions $d$ has vertices $p_k = \sum_{0 \le i < k} s(d_i)$ for $k = 0, \dots, n-1$ (so $p_0 = 0$; vertex indices are also taken modulo $n$). Let $U(a, b)$ be the number of horizontal steps $k$ with $\min(x(p_k), x(p_{k+1})) = a$ and $y(p_k) > b$. Then for all integers $a, b$,

$$U(a, b) = U(a, b + 1) + |H_{a, b+1}|,$$

where $H_{a, b+1}$ is the set of horizontal steps $k$ with $\min(x(p_k), x(p_{k+1})) = a$ and $y(p_k) = b + 1$.
