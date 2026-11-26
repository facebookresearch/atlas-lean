# Sufficient statistic for a discrete family

Let $X$, $\Theta$ and $\mathcal{T}$ be sets, $(p_\theta)_{\theta \in \Theta}$ a family of probability mass functions on $X$ and $T : X \to \mathcal{T}$ a statistic, with $P_\theta(T = t) = \sum_{x : T(x) = t} p_\theta(x)$. The statistic $T$ is sufficient for $(p_\theta)$ if the conditional probability $p_\theta(x) / P_\theta(T = T(x))$ of $x$ given $T = T(x)$ is the same under any two parameters $\theta, \theta'$ for which $P_\theta(T = T(x)) > 0$ and $P_{\theta'}(T = T(x)) > 0$.

## Sources

- R. A. Fisher, *On the mathematical foundations of theoretical statistics*, Philos. Trans. Roy. Soc. London Ser. A 222 (1922), 309–368.
- J. Neyman, *Su un teorema concernente le cosiddette statistiche sufficienti*, Giorn. Ist. Ital. Attuari 6 (1935), 320–334.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Definition 6.2.1.
