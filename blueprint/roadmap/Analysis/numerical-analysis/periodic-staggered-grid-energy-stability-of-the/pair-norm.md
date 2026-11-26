# Pair norm

For $h \in \mathbb{R}$ and $u, v \in \mathbb{R}^N$, let $S_h(w) = h \sum_j w_j^2$ and let the pair norm be $\|(u, v)\|_h = \sqrt{S_h(u) + S_h(v)}$, with $\sqrt{\cdot} = 0$ on negative numbers. For $h \ge 0$, $S_h$ is the square of the weighted grid norm and the pair norm is $\sqrt{h}$ times the Euclidean norm of the concatenated vector $(u, v) \in \mathbb{R}^{2N}$: with one cell and $(u, v) = (1, 0)$ it is $2$ at $h = 4$ and $0$ at $h = 0$, while the Euclidean norm is $1$. For $h < 0$, $S_h$ can be negative.
