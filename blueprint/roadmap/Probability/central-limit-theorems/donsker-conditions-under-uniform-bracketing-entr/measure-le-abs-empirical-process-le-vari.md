# Chebyshev's inequality

**Chebyshev's inequality** for the empirical process. Let $(\Omega, P)$ be a probability space and $X_0, X_1, \dots : \Omega \to S$ mutually independent random variables, each with law $\mu$: almost everywhere measurable with pushforward $\mu$ under $P$, not necessarily measurable everywhere. $\mathbb{G}_n$ is the [empirical process](empirical-process.md), $0$ when $n = 0$. Let $h : S \to \mathbb{R}$ be measurable with $h \in L^2(\mu)$, and let $t > 0$. Then for every $n \in \mathbb{N}$, with $\mathbb{G}_n h = n^{-1/2} \sum_{k<n} (h(X_k) - \int h \, d\mu)$,

$$P\big(\lvert \mathbb{G}_n h \rvert \ge t\big) \le \frac{\mathrm{Var}_\mu[h]}{t^2}.$$
