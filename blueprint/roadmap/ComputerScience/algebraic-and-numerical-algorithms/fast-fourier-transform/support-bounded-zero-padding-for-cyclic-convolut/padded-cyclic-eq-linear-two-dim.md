# Zero padding turns two-dimensional cyclic convolution into linear convolution

For an array $x \in \mathbb{C}^{M \times K}$ let $\bar x_{i,j} = x_{i,j}$ for $i < M$, $j < K$ and $\bar x_{i,j} = 0$ for all other $(i, j) \in \mathbb{N}^2$. The linear convolution of $x \in \mathbb{C}^{M \times K}$ and $y \in \mathbb{C}^{P \times Q}$ is

$$(x * y)_{t_1, t_2} = \sum_{i=0}^{t_1} \sum_{j=0}^{t_2} \bar x_{i,j}\, \bar y_{t_1 - i,\, t_2 - j}.$$

For $N_1, N_2 \ge 1$ the zero extension of $x$ to $\mathbb{Z}/N_1 \times \mathbb{Z}/N_2$ is $x^{(N_1,N_2)}(i, j) = \bar x_{\tilde i, \tilde j}$ with $\tilde i, \tilde j$ the least nonnegative representatives, and the cyclic convolution of $a, b : \mathbb{Z}/N_1 \times \mathbb{Z}/N_2 \to \mathbb{C}$ is $(a \circledast b)(p_1, p_2) = \sum_{i \in \mathbb{Z}/N_1} \sum_{j \in \mathbb{Z}/N_2} a(i, j)\, b(p_1 - i, p_2 - j)$.

Let $M, K, P, Q \ge 1$ and $N_1, N_2 \ge 1$ with $M + P - 1 \le N_1$ and $K + Q - 1 \le N_2$. Then for all naturals $t_1 < M + P - 1$ and $t_2 < K + Q - 1$,

$$\bigl(x^{(N_1,N_2)} \circledast y^{(N_1,N_2)}\bigr)(t_1 \bmod N_1,\, t_2 \bmod N_2) = (x * y)_{t_1, t_2}.$$
