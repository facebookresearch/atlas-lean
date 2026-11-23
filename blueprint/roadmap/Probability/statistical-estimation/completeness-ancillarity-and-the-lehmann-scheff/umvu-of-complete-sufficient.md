# Lehmann–Scheffé theorem

Let $(\Omega, \mathcal{F})$ and $\mathcal{T}$ be measurable spaces and $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $\Omega$. A statistic $S : \Omega \to \mathcal{T}$ is complete for $(P_\theta)$ if it is measurable and every measurable $a : \mathcal{T} \to \mathbb{R}$ such that $a(S)$ is $P_\theta$-integrable with $\mathbb{E}_{P_\theta}[a(S)] = 0$ for every $\theta$ satisfies $a(S) = 0$ $P_\theta$-almost everywhere for every $\theta$. Call an estimator $W : \Omega \to \mathbb{R}$ unbiased for a target $\tau : \Theta \to \mathbb{R}$ if $W$ is $P_\theta$-integrable with $\mathbb{E}_{P_\theta}[W] = \tau(\theta)$ for every $\theta$. Suppose $S$ is complete and the σ-algebra $\sigma(S)$ it generates is [sufficient](../sufficient-statistics-and-the-factorization-theo/is-sufficient.md) for $(P_\theta)$, and let $W$ be a measurable estimator, unbiased for $\tau$, with $\mathbb{E}_{P_\theta}[W^2] < \infty$ for every $\theta$. Then there is a measurable $\varphi : \mathcal{T} \to \mathbb{R}$ such that

- $\varphi(S)$ is unbiased for $\tau$;
- $\varphi(S) = \mathbb{E}_{P_\theta}[W \mid \sigma(S)]$ $P_\theta$-almost everywhere, for every $\theta$;
- $\operatorname{Var}_{P_\theta}(\varphi(S)) \le \operatorname{Var}_{P_\theta}(W')$ for every $\theta$ and every measurable estimator $W'$ unbiased for $\tau$ with $\mathbb{E}_{P_\theta}[(W')^2] < \infty$ for every $\theta$.

So $\varphi(S)$ is a uniformly minimum-variance unbiased estimator of $\tau$.

## Sources

- E. L. Lehmann and H. Scheffé, "Completeness, similar regions, and unbiased estimation. Part I", *Sankhyā* 10 (1950), 305–340.
