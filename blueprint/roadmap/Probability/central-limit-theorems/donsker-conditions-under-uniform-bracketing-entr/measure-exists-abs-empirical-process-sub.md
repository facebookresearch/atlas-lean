# Asymptotic equicontinuity of the empirical process under uniform bracketing entropy

Let $(\Omega, P)$ be a probability space, $\mu$ a probability measure on a measurable space $S$, and $X_0, X_1, \dots : \Omega \to S$ mutually independent random variables, each with law $\mu$: almost everywhere measurable with pushforward $\mu$ under $P$, not necessarily measurable everywhere. $\mathbb{G}_n$ is the [empirical process](empirical-process.md), $0$ when $n = 0$. Let $(F_i)_{i \in \iota}$ be measurable functions $S \to \mathbb{R}$ in $L^2(\mu)$ whose uniform bracketing entropy integral is finite,

$$\int_{(0,1]} H(\varepsilon) \, d\varepsilon < \infty,$$

where $H(\varepsilon) \in [0, \infty]$ is the [uniform bracketing entropy](uniform-bracketing-entropy.md), the infimum of $\sqrt{\log n}$ over the sizes $n$ of uniform bracket covers of width $\varepsilon$, with $\log 0 = 0$; for instance the empty family has a cover by zero brackets, so its entropy is $0$.

Write $\mathbb{G}_n f = n^{-1/2} \sum_{k<n} (f(X_k) - \int f \, d\mu)$. Then for every $\varepsilon > 0$ and $\eta > 0$ there is $\delta > 0$ such that for every $n \in \mathbb{N}$,

$$P^*\Big( \exists\, i, j :\ \mathrm{Var}_\mu[F_i - F_j] < \delta^2 \ \text{and}\ \lvert \mathbb{G}_n F_i - \mathbb{G}_n F_j \rvert > \varepsilon \Big) \le \eta,$$

where $P^*$ is the outer measure of $P$, so the event need not be measurable. The quantity $\rho_\mu(f, g) = \sqrt{\mathrm{Var}_\mu[f - g]}$ is the standard-deviation semimetric. The bound holds for every $n$, which is stronger than the usual $\limsup$ form.
