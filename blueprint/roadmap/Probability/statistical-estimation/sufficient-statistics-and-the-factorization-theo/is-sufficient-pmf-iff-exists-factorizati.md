# The Fisher–Neyman factorization theorem

Let $X$, $\Theta$ and $\mathcal{T}$ be sets, $(p_\theta)_{\theta \in \Theta}$ a family of probability mass functions on $X$ and $T : X \to \mathcal{T}$ a statistic, with $P_\theta(T = t) = \sum_{x : T(x) = t} p_\theta(x)$. Then $T$ is [sufficient](is-sufficient-pmf.md) for $(p_\theta)$ if and only if there are functions $g_\theta : \mathcal{T} \to [0, \infty)$ and $h : X \to [0, \infty)$, with $h$ free of $\theta$, such that

$$p_\theta(x) = g_\theta(T(x))\, h(x) \quad \text{for all } \theta, x.$$

## Sources

- R. A. Fisher, *On the mathematical foundations of theoretical statistics*, Philos. Trans. Roy. Soc. London Ser. A 222 (1922), 309–368.
- J. Neyman, *Su un teorema concernente le cosiddette statistiche sufficienti*, Giorn. Ist. Ital. Attuari 6 (1935), 320–334.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Theorem 6.2.6.
