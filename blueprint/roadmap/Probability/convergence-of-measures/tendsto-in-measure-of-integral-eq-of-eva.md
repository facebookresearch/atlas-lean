# Chebyshev consistency

Let $\mu$ be a measure on $\Omega$, $l$ a filter on an index set $\iota$, and $\theta \in \mathbb{R}$. Let $T_n : \Omega \to \mathbb{R}$, $n \in \iota$, be almost everywhere strongly measurable with $\int T_n \, d\mu = \theta$ for every $n$, where the Bochner integral is $0$ when $T_n$ is not integrable (so for $\theta = 0$ the hypothesis allows non-integrable $T_n$). Suppose the extended variances

$$\operatorname{Var}_\mu(T_n) = \int^{-} (T_n - \theta)^2 \, d\mu \in [0, \infty]$$

tend to $0$ along $l$. Then $T_n \to \theta$ in measure along $l$: for every $\varepsilon > 0$,

$$\mu(\{\omega : |T_n(\omega) - \theta| \ge \varepsilon\}) \to 0 \quad \text{along } l.$$
