# Two-dimensional zero extension to cyclic indices

For $M, K, N_1, N_2 \in \mathbb{N}$ and an array $x \in \mathbb{C}^{M \times K}$, the zero extension $x^{(N_1,N_2)} : \mathbb{Z}/N_1 \times \mathbb{Z}/N_2 \to \mathbb{C}$ is

$$x^{(N_1,N_2)}(i, j) = \begin{cases} x_{\tilde i, \tilde j} & \text{if } \tilde i < M \text{ and } \tilde j < K, \\ 0 & \text{otherwise,} \end{cases}$$

where $\tilde i$ and $\tilde j$ are the natural-number values of $i$ and $j$: the least nonnegative representatives when $N_k \ge 1$, and the absolute value of the integer when $N_k = 0$ (in which case $\mathbb{Z}/0 = \mathbb{Z}$).
