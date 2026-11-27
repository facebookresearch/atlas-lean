# Interspecies correlation under Brownian motion with speciational jumps

**Model (Yule–Brownian-motion–jumps).** A phylogeny is a Yule tree with rate $\lambda=1$ conditioned on $n$ tips. A trait evolves along each branch as Brownian motion with variance rate $\sigma_a^2$ (anagenetic change). At each speciation event, independently on each daughter lineage, a jump with mean $0$ and variance $\sigma_c^2<\infty$ is added with probability $p$ (cladogenetic change). Put

$$\kappa=\frac{2p\sigma_c^2}{\sigma_a^2+2p\sigma_c^2}\in[0,1),$$

the share of the long-run per-lineage variance due to jumps. Let $X$ be the trait of a uniformly chosen tip and $X_1,X_2$ the traits of two distinct uniformly chosen tips; all moments are unconditional on the tree.

**Theorem 3.1.**

$$\operatorname{Var}[X]=(\sigma_a^2+2p\sigma_c^2)H_n-2p\sigma_c^2, \qquad \operatorname{Cov}[X_1,X_2]=\frac{2(n-H_n)}{n-1}(\sigma_a^2+2p\sigma_c^2)-2p\sigma_c^2,$$

so the interspecies correlation is

$$\rho_n=\frac{\frac{2(n-H_n)}{n-1}-\kappa}{H_n-\kappa}.$$

As $n\to\infty$, $\operatorname{Var}[X]\sim(\sigma_a^2+2p\sigma_c^2)\ln n$, $\operatorname{Cov}[X_1,X_2]\to 2\sigma_a^2+2p\sigma_c^2$ and $\rho_n\sim(2-\kappa)/\ln n$. For fixed $n$, $\rho_n$ decreases in $\kappa$, with limit $\bigl(n-2(H_n-\tfrac12)\bigr)/\bigl((n-1)(H_n-1)\bigr)\ge 0$ as $\kappa\to 1$. A general rate $\lambda$ is absorbed by replacing $\sigma_a^2$ with $\sigma_a^2/\lambda$.

**Constrained version (Theorem 3.2).** If the Brownian motion is replaced by an Ornstein–Uhlenbeck process $dX=-\alpha(X-\theta)dt+\sigma_a dB$ and one daughter lineage receives a jump at each speciation, the mean is $\mathbb{E}[X]=b_{n,\alpha}X_0+(1-b_{n,\alpha})\theta$ with $b_{n,\alpha}=\Gamma(n+1)\Gamma(\alpha+1)/\Gamma(n+\alpha+1)$, and the variance, covariance and correlation are explicit $\kappa$-weighted mixtures of an anagenetic and a cladogenetic part. The fitted $\kappa$ then quantifies the proportion of trait change attributable to speciation.

## Expansion

Because jumps are independent of the Brownian motion and have mean zero, the variance of a tip is $\sigma_a^2\,\mathbb{E}[T]+p\sigma_c^2\,\mathbb{E}[\Upsilon]$ with tree height $T$ and lineage depth $\Upsilon$, and the covariance of two tips is $\sigma_a^2\,\mathbb{E}[T-\tau]+p\sigma_c^2\,\mathbb{E}[\upsilon]$, where $\tau$ is the time back to their most recent common ancestor and $\upsilon$ the number of shared speciation events above it. Substituting $\mathbb{E}[T]=H_n$, $\mathbb{E}[\tau]=\frac{n+1}{n-1}H_n-\frac{2n}{n-1}$ and the [speciation-count means](speciation-event-counts-on-a-conditioned-yule-tree.md) $\mathbb{E}[\Upsilon]=2H_n-2$, $\mathbb{E}[\upsilon]=\frac{4(n-H_n)}{n-1}-2$ gives the formulas; jumps correct numerator and denominator of the pure Brownian correlation by the same $\kappa$.

## Depends on

- [Speciation event counts on a conditioned Yule tree](speciation-event-counts-on-a-conditioned-yule-tree.md)

## Sources

- Krzysztof Bartoszek, "Quantifying the effects of anagenetic and cladogenetic evolution", arXiv:1305.2378 (2013), Section 3 (model definitions, the theorem for the unconstrained model with its proof and asymptotics, Theorem 3.2 for the Ornstein–Uhlenbeck model), Appendix A (proof of Theorem 3.2), <https://doi.org/10.48550/arXiv.1305.2378>. Published version: Mathematical Biosciences 254 (2014), 42–57, <https://doi.org/10.1016/j.mbs.2014.06.002>; locators above refer to the arXiv version.
