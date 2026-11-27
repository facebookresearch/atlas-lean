# Kullback-Leibler divergence between multivariate Gaussians

Let $\iota$ be a nonempty finite index set, $n = |\iota| \ge 1$, $m, q \in \mathbb{R}^\iota$, and $S, T$ positive definite. Then, in nats,

$$D_{\mathrm{KL}}\bigl(\mathcal{N}(m, S) \,\|\, \mathcal{N}(q, T)\bigr) = \frac12 \Bigl( \ln \frac{\det T}{\det S} - n + \operatorname{tr}(T^{-1} S) + (m - q)^\top T^{-1} (m - q) \Bigr).$$
