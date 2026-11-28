# Distance law of the random series-parallel graph

Let $p \in \mathbb{R}$ and let $\bar p = \min(\max(p, 0), 1)$ be $p$ clamped to $[0, 1]$. The laws $\mathcal{L}_n(p)$ on $\mathbb{N}$ of the distance $D_n(p)$ between the two extremal vertices of the Hambly–Jordan random series-parallel graph after $n$ steps are defined recursively: $\mathcal{L}_0(p)$ is the point mass at $1$, and $\mathcal{L}_{n+1}(p)$ is the law of

$$D_{n+1} = \begin{cases} D_n + D_n' & \text{if } E_n = 1, \\ \min(D_n, D_n') & \text{if } E_n = 0, \end{cases}$$

where $D_n, D_n'$ are independent with law $\mathcal{L}_n(p)$ and $E_n$ is an independent Bernoulli($\bar p$) variable. This is the recursion (1.1) of Chen, Derrida, Duquesne and Shi: in the graph every edge is replaced independently by two edges in series with probability $\bar p$ ($E_n = 1$) or by two parallel edges otherwise.
