# Discrete factorization, necessity

Let $X$, $\Theta$ and $\mathcal{T}$ be sets, $(p_\theta)_{\theta \in \Theta}$ a family of probability mass functions on $X$ and $T : X \to \mathcal{T}$ a statistic, with $P_\theta(T = t) = \sum_{x : T(x) = t} p_\theta(x)$. If $T$ is [sufficient](is-sufficient-pmf.md) for $(p_\theta)$, then there is $h : X \to [0, 1]$, free of $\theta$, with

$$p_\theta(x) = P_\theta(T = T(x))\, h(x) \quad \text{for all } \theta, x.$$
