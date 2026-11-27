# Pairwise coalescence time in the spatial Λ-Fleming–Viot process as a Cox process

**Setting.** Consider the Gaussian version of the spatial $\Lambda$-Fleming–Viot process (SLFV) on $\mathbb{R}^2$. Reproduction events occur at Poisson rate $\lambda$ per unit area and time. An event centred at $z$ draws a parental location $w$ from the Gaussian density $(2\pi\theta^2)^{-1}\exp(-\|z-w\|^2/(2\theta^2))$ and a parental type from the population at $w$; at each location $z'$ a fraction $p(z',z) = u_0\exp(-\|z'-z\|^2/(2\theta^2))$ of the population is then replaced by offspring of that type. Backwards in time, a lineage at $x$ is hit by an event centred at $z$ with probability $p(x,z)$ and then jumps to the parental location, approximately Gaussian with mean $z$ and covariance $\theta^2 I$ (exactly so in the high-density limit). For the ball-shaped events of the disc model the pair coalescence rate is instead an overlap-volume kernel, as for the [two-lineage process with ball-shaped events](slfv-dual-lineage-process-under-the-integrabilit.md). Integrating the product $p(x,z)\,p(y,z)$ of the two hit probabilities over event centres $z$, two lineages at squared distance $d = \|x-y\|^2$ are both hit, and merge, at rate

$$\rho^*_{X\wedge Y}(d) = \pi\theta^2u_0^2\lambda\,\exp\Big(-\frac{d}{4\theta^2}\Big).$$

Let $D_t = \|X_t - Y_t\|^2$, $Z_t = D_t/(4\theta^2)$, and $T_0$ be the coalescence time of two lineages started at squared distance $d_0 = D_0$.

**Proposition (hazard representation).**

$$\Pr(T_0 > t \mid d_0) = \exp\Big(-\pi\theta^2u_0^2\lambda\int_0^t\mathbb{E}\big[e^{-Z_u} \,\big|\, T_0 > u, d_0\big]\,du\Big).$$

Equivalently, with $\mathcal{M}_{Z_t}(s) = \mathbb{E}[e^{-sZ_t}\mathbf{1}_{T_0>t} \mid d_0]$, one has $\Pr(T_0 \le t \mid d_0) = 1 - \mathcal{M}_{Z_t}(0)$, the conditional coalescence hazard is $\pi\theta^2u_0^2\lambda\,\mathcal{M}_{Z_t}(1)/\mathcal{M}_{Z_t}(0)$, and $\partial_s^k\mathcal{M}_{Z_t}(0)/\mathcal{M}_{Z_t}(0) = \mathbb{E}[(-Z_t)^k \mid T_0 > t, d_0]$; $\partial_t\mathcal{M}_{Z_t}(s)$ has a closed form, giving a closed system for these moments.

**Proposition (Cox-process description).** Let the two lineages move by the non-coalescing dynamics only, producing a random path $\delta(t)$ of their **squared** distance, and place potential coalescence events as a Poisson process with intensity $\rho(t) = \pi\theta^2u_0^2\lambda\exp(-\delta(t)/(4\theta^2))$. The first such event has the law of $T_0$:

$$\Pr(T_0 \le t \mid d_0) = 1 - \mathbb{E}\Big[\exp\Big(-\int_0^t\rho(u)\,du\Big)\Big].$$

On a bounded rectangular habitat the same representation holds with a position-dependent coalescence rate accounting for events truncated at the boundary, and $T_0$ is approximately exponential after the lineages' positions have mixed.

## Expansion

The hazard identity follows from $\Pr(T_0 \le t + h \mid T_0 > t) = h\,\mathbb{E}[\rho^*(D_t) \mid T_0 > t] + o(h)$, integrating the resulting ODE for $\log\Pr(T_0 > t)$. Conditioning on the whole path of the non-coalescing motion turns coalescence into a doubly stochastic (Cox) process, so $T_0$ is a mixed exponential; the expectation of the exponential replaces the exponential of the expectation in the hazard form. Approximating the conditional law of $Z_t$ by a Gamma distribution matched to its first two moments gives simple, accurate closed-form approximations of the distribution of $T_0$ on the plane, and the analysis bears on whether the SLFV genealogy comes down from infinity.

## Sources

- Johannes Wirtz and Stéphane Guindon, "Rate of coalescence of lineage pairs in the spatial Λ-Fleming–Viot process", *Theoretical Population Biology* 146 (2022), 15–28, <https://doi.org/10.1016/j.tpb.2022.05.002>. Numbering as in the preprint arXiv:2109.05833v1, <https://arxiv.org/abs/2109.05833v1>: Section 2 (SLFV dynamics and coalescence rate), Section 3 (ODE and Cox-process representations, rectangle case) and Sections 4–5 (dynamics of $Z_t$ and approximations).
