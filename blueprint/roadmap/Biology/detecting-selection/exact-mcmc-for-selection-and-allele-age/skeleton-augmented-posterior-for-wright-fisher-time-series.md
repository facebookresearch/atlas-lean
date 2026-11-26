# Skeleton-augmented posterior for Wright–Fisher time series

**Model.** At sampling times $t_1<\dots<t_K$, $y_i$ of $n_i$ sampled chromosomes carry an allele, with $Y_i\mid X_{t_i}=x_i\sim\mathrm{Binomial}(n_i,x_i)$ independently. The allele frequency is $X\equiv0$ before the allele's birth time $t_0$ and afterwards follows the non-neutral Wright–Fisher diffusion
$$dX_t=\tfrac12\big(\sigma X_t(1-X_t)\eta(X_t)-\theta_2X_t+\theta_1(1-X_t)\big)dt+\sqrt{X_t(1-X_t)}\,dW_t,$$
with selection strength $\sigma$, a polynomial $\eta$ encoding dominance or frequency dependence, and known recurrent mutation $\theta=(\theta_1,\theta_2)$. Priors $q_1(\sigma)q_2(\eta)q_3(t_0)$ give the posterior $p(\sigma,\eta,t_0\mid y)\propto q_1q_2q_3\,\ell(y\mid\sigma,\eta,t_0)$, where
$$\ell(y\mid\sigma,\eta,t_0)=\int_{[0,1]^K}\prod_{i=1}^K\mathcal B_{n_i,x_i}(y_i)\,p^\theta_{\sigma,\eta}(t_i-t_{i-1},x_{i-1},x_i)\,dx_i$$
involves the intractable transition density $p^\theta_{\sigma,\eta}$.

**Augmented density.** Exact simulation of the non-neutral diffusion and its bridges is a rejection scheme against neutral Wright–Fisher paths: by Girsanov's theorem the Radon–Nikodym derivative is $\exp\{A_{\sigma,\eta}(X_T)-A_{\sigma,\eta}(X_0)-\int\varphi_{\sigma,\eta}(X_s)\,ds\}$ with a polynomial $A_{\sigma,\eta}$ and
$$\varphi_{\sigma,\eta}(x)=\frac\sigma4\Big(\big(-\theta_2x+\theta_1(1-x)\big)\eta(x)+x(1-x)\big(\tfrac\sigma2\eta(x)^2+\eta'(x)\big)\Big),$$
and the integral is handled by a Poisson process of skeleton points. With the latent values $X=(X_i)$ at sampling times and skeleton points $\Phi=(\Phi_i)$, the joint density
$$p(\sigma,\eta,t_0,y,X,\Phi)=q_1(\sigma)q_2(\eta)q_3(t_0)\,e^{A_{\sigma,\eta}(X_K)-(t_K-t_0)\varphi^-_{\sigma,\eta}}\prod_{i=1}^K\mathcal B_{n_i,X_i}(y_i)\,f(\sigma,\eta,\Phi_i,X_i)$$
is explicit ($\varphi^-_{\sigma,\eta}$ is a lower bound of $\varphi_{\sigma,\eta}$ and $f$ is an explicit function of the skeleton). Its marginal in $(\sigma,\eta,t_0)$ is the exact posterior, so a Metropolis-within-Gibbs sampler that updates path segments (initial, interior and end segments, including the birth time) by exact bridge simulation and the parameters by Metropolis steps on this density targets the exact posterior.

## Depends on

- [Exact simulation of the Wright–Fisher diffusion](../../population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/exact-simulation-of-the-wright-fisher-diffusion.md)
- [HMM likelihood for allele-frequency time series](../selection-from-allele-frequency-time-series/hmm-likelihood-for-allele-frequency-time-series.md)

## Expansion

Acceptance probabilities for parameter updates would ordinarily require ratios of transition densities. In the augmented space the path is represented by its values at sampling times and the points of a Poisson process used to accept or reject a neutral proposal; given these, the likelihood ratio between two parameter values is a ratio of explicit Girsanov factors, so every acceptance probability is computable. The price is extra latent variables to update and some loss of mixing, but no time discretization or numerical PDE solution is involved.

## Sources

- J. Sant, P. A. Jenkins, J. Koskela, D. Spano, "Bayesian inference from time series of allele frequency data using exact simulation techniques", arXiv:2502.12279 (2025), Section 2 (model (WFDiff), augmented likelihood (AugmentedLikelihoodGlobal), updating procedure), <https://doi.org/10.48550/arXiv.2502.12279>.
