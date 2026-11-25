# Vanishing of the cross terms in Wald's second equation

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be identically distributed real random
variables with $X_0$ integrable and $\mathbb{E}[X_0] = 0$, let $(\mathcal{F}_k)$ be a filtration
such that each $X_k$ is independent of $\mathcal{F}_k$ and $\mathcal{F}_{k+1}$-measurable, and let
$T$ be an $\mathbb{N}$-valued stopping time. Suppose that the stopped cross-term series is
absolutely summable:
$\sum_n \mathbb{E}\big[\big|\mathbf{1}_{\{n < T\}} \sum_{j < n} X_j X_n\big|\big] < \infty$. Then

$$\mathbb{E}\Big[\sum_{i < T} \sum_{j < i} X_j X_i\Big] = 0 .$$
