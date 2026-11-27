# Poisson sampling of the Feller diffusion and its coalescent point process

**Setting.** The Feller diffusion with parameter $\alpha \in \mathbb R$ has generator $\mathcal L = \tfrac12 x\,\partial_{xx} + \alpha x\,\partial_x$ on $[0, \infty)$; it is the limit of linear birth–death processes whose birth and death rates diverge with fixed difference $\alpha$ (critical, super- or sub-critical according to the sign of $\alpha$). Start from one founder at time $0$ and stop at time $t$. *Poisson sampling with parameter $\nu > 0$* draws $\mathrm{Pois}(2\nu x)$ individuals when the population is $X(t) = x$; it is the limit of Bernoulli sampling with probability $2\nu\epsilon$ of the rescaled birth–death process $X = \lim \epsilon N_\epsilon$.

**Theorem.**
1. The coalescent tree of a Poisson-sampled Feller diffusion is a coalescent point process (CPP). For $\alpha \ne 0$ its node-height distribution function is

$$F_H(\tau) = \frac{e^{\delta \tau} - 1}{e^{\delta\tau} - 1 + \gamma_\nu}, \qquad \delta = |\alpha|, \quad \gamma_\nu = \frac{|\alpha|}{\max(\nu, \nu - \alpha)},$$

the same algebraic form as for a Bernoulli-sampled birth–death process. In the critical case $\alpha = 0$, where $\delta = \gamma_\nu = 0$ and the expression above is undefined, the node-height distribution function is

$$F_H(\tau) = \frac{\tau}{\tau + 1/\nu}.$$

2. *(Uniform samples as mixtures.)* Let $\Pi^{(\alpha)}_k$ be the law of the coalescent tree of $k$ individuals sampled uniformly from $X(t)$, and $\Gamma^{(\alpha)}_{\nu,k}$ the law of the Poisson-sampled tree conditioned on $k$ tips. Then

$$\Pi^{(\alpha)}_k = \int_0^\infty \Gamma^{(\alpha)}_{\nu,k}\, \mu_k(d\nu), \qquad \mu_k(d\nu) = \frac{k\,v^{k-1}}{(1+v)^{k+1}}\, dv, \quad v = 2\nu\,\beta(t; |\alpha|),$$

where $\beta(t;\alpha)$ is the time-scale function of the [Poisson-gamma transition law](poisson-gamma-transition-law-of-the-feller-diffusion.md), so $\beta(t;|\alpha|) = (e^{|\alpha| t}-1)/(2|\alpha|)$ for $\alpha \ne 0$ and $\beta(t;0) = t/2$.
3. *(Super/sub-critical duality.)* A Poisson-sampled super-critical diffusion with $\nu > \alpha > 0$ has the same distribution of coalescent times as the Poisson-sampled sub-critical diffusion with parameter $-\alpha$ and sampling rate $\nu - \alpha$, and conversely every sub-critical $(\alpha < 0, \nu)$ corresponds to the super-critical $(-\alpha, \nu - \alpha)$; if $\alpha > \nu > 0$ no sub-critical counterpart exists.

## Depends on

- [Poisson-gamma transition law of the Feller diffusion](poisson-gamma-transition-law-of-the-feller-diffusion.md)

## Proof idea

A CPP tree is encoded by i.i.d. node heights $H_1, H_2, \dots$ stopped at the first exceeding $t$; Bernoulli sampling of a birth–death CPP is again a CPP with a modified node-height law, and passing to the diffusion limit with sampling probability proportional to $\epsilon$ keeps $\gamma$ finite, giving item 1. Item 2 transfers Lambert's theorem that uniform $k$-samples of a CPP are mixtures of Bernoulli-sampled CPPs over the sampling probability; in the limit the mixing variable is the Poisson intensity. Item 3 follows because the node-height law depends on $(\alpha, \nu)$ only through $(|\alpha|, \gamma_\nu)$. For $\alpha \ne 0$ and an improper uniform prior on $t$, the expected inter-coalescence times of a sample of $n$ are hypergeometric functions $\frac{\gamma}{\delta}\frac{1}{k}\,{}_2F_1(n-k+1, 1; n+1; 1-\gamma)$.

## Sources

- C. J. Burden and R. C. Griffiths, "The Feller diffusion as the limit of a coalescent point process", Theoretical Population Biology 171 (2026), 47–58, <https://doi.org/10.1016/j.tpb.2026.07.001>. Numbering as in the preprint arXiv:2601.03599v2, <https://arxiv.org/abs/2601.03599v2>: Section 5.2, Eqs. (27)–(29) (node-height law, including the critical case) and Corollary 1 (duality); Theorem 4 (uniform samples); Theorem 6, Eq. (37) (expected inter-coalescence times).
