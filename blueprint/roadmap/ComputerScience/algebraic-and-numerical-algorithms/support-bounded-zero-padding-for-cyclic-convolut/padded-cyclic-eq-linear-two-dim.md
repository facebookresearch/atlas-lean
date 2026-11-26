# Zero padding to the full support makes two-dimensional cyclic convolution linear

Let $M, K, P, Q \ge 1$ and $N_1 \ge M + P - 1$, $N_2 \ge K + Q - 1$ be natural numbers, and let $x$ be an $M \times K$ array and $y$ a $P \times Q$ array, with [zero extensions](zero-extend2.md) $x^{(N_1, N_2)}$ and $y^{(N_1, N_2)}$. Then for all natural numbers $t_1 < M + P - 1$ and $t_2 < K + Q - 1$,

$$\bigl(x^{(N_1, N_2)} \circledast y^{(N_1, N_2)}\bigr)(t_1 \bmod N_1, t_2 \bmod N_2) = (x * y)(t_1, t_2),$$

where $(a \circledast b)(p) = \sum_{i \in \mathbb{Z}/N_1\mathbb{Z}} \sum_{j \in \mathbb{Z}/N_2\mathbb{Z}} a(i, j)\, b(p_1 - i, p_2 - j)$ is cyclic convolution on $\mathbb{Z}/N_1\mathbb{Z} \times \mathbb{Z}/N_2\mathbb{Z}$ and $*$ is the [linear convolution of arrays](linear-convolution2.md). This is the [one-dimensional padding bound](padded-cyclic-eq-linear.md) in each coordinate.
