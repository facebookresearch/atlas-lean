# The Rao–Blackwell theorem for a sufficient statistic

Let $(\Omega, \mathcal{F})$ be a measurable space, $(P_\theta)_{\theta \in \Theta}$ probability measures on it, and $T : \Omega \to \mathcal{T}$ a measurable statistic whose σ-algebra $\sigma(T)$ is [sufficient](../sufficient-statistics-and-the-factorization-theo/is-sufficient.md) for $(P_\theta)$. Let $W$ be a measurable real estimator with $\mathbb{E}_{P_\theta} W^2 < \infty$ for every $\theta$, and $\tau : \Theta \to \mathbb{R}$ a target. Then there is a measurable $\varphi : \mathcal{T} \to \mathbb{R}$ such that for every $\theta$:

- $\varphi(T) = \mathbb{E}_{P_\theta}[W \mid T]$ $P_\theta$-almost everywhere;
- $\mathbb{E}_{P_\theta}\varphi(T) = \mathbb{E}_{P_\theta} W$;
- $\mathbb{E}_{P_\theta} (W - \tau(\theta))^2 = \mathbb{E}_{P_\theta} (\varphi(T) - \tau(\theta))^2 + \mathbb{E}_{P_\theta} (W - \varphi(T))^2$.

## Sources

- C. R. Rao, *Information and the accuracy attainable in the estimation of statistical parameters*, Bull. Calcutta Math. Soc. 37 (1945), 81–91.
- D. Blackwell, *Conditional expectation and unbiased sequential estimation*, Ann. Math. Statist. 18 (1947), 105–110.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Section 7.3.
