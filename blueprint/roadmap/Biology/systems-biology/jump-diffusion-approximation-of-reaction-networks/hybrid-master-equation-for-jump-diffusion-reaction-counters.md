# Hybrid master equation for jump-diffusion reaction counters

**Model.** A network has reactions $R_k:\sum_j\underline\mu_{jk}S_j\xrightarrow{\phi_k}\sum_j\bar\mu_{jk}S_j$, $k=1,\dots,r$, with stoichiometric vectors $\mu_k=\bar\mu_{\cdot k}-\underline\mu_{\cdot k}$ and mass-action propensities $\gamma_k(x)=\phi_k\prod_j\binom{x_j}{\underline\mu_{jk}}$. The reactions are split into slow ones $\mathcal D$ and fast ones $\mathcal C$. With independent unit Poisson processes $\zeta_i$ and Brownian motions $W_j$,

$$X(t)=X(0)+\sum_{i\in\mathcal D}\zeta_i\Big(\int_0^t\gamma_i(X(s))ds\Big)\mu_i+\sum_{j\in\mathcal C}\Big[\int_0^t\gamma_j(X(s))ds+W_j\Big(\int_0^t\gamma_j(X(s))ds\Big)\Big]\mu_j .$$

Equivalently $X(t)=X(0)+\sum_{i\in\mathcal D}U_i(t)\mu_i+\sum_{j\in\mathcal C}V_j(t)\mu_j$, with integer slow counters $U$, real fast counters $V$, and propensities $\kappa_k(u,v)=\gamma_k(X)$ expressed in the counters.

**Theorem (hybrid master equation).** Given the history $\mathcal H$, the time-marginal density $p(u,v,t\mid\mathcal H)$ of $(U,V)$ satisfies $\partial_tp=\mathscr Dp+\mathscr Cp$ with $p(u,v,0)=\delta(u)\delta(v)$, where

$$\mathscr Dp(u,v)=\sum_{i\in\mathcal D}\big[\kappa_i(u-e_i,v)\,p(u-e_i,v)-\kappa_i(u,v)\,p(u,v)\big],$$

$$\mathscr Cp(u,v)=-\sum_{j\in\mathcal C}\partial_{v_j}\big(\kappa_j(u,v)\,p\big)+\frac12\sum_{j\in\mathcal C}\partial^2_{v_j}\big(\kappa_j(u,v)\,p\big).$$

This is a generalized Fokker–Planck equation: a chemical master equation in the slow counters coupled to a Fokker–Planck equation in the fast ones, each fast counter having drift and diffusion coefficient both equal to its propensity.

**Inference.** For noisy, partial observations $Y_{1:m}$ of $X$ at discrete times, the joint posterior of the path and the rate constants $\Phi$ is sampled by a blocked Gibbs particle smoother: forward bootstrap filtering and backward smoothing of the latent jump-diffusion path, alternating with parameter updates split into blocks to avoid the degeneracy of alternating path and diffusion-parameter updates.

## Expansion

The random time change representation writes each counter as a unit-rate process run at the integrated propensity. For a fast reaction the Poisson process $\zeta(\Lambda)$ is replaced by $\Lambda+W(\Lambda)$, its diffusion (central limit) approximation with mean and variance $\Lambda$; this yields drift and diffusion coefficients equal to $\kappa_j$ in the Fokker–Planck part. The slow counters keep unit jumps at rate $\kappa_i$, which gives the master-equation part. The two parts couple only through the propensities, which depend on both counters.

## Sources

- D. Altıntan, B. Alt, H. Koeppl, "Bayesian Inference for Jump-Diffusion Approximations of Biochemical Reaction Networks", arXiv:2304.06592 (2023), Section 2 (model, Eqs. (states), (dis\_count), (cont\_count\_u)), Theorem 1, Section 4 (posterior inference, blocked Gibbs particle smoothing), <https://doi.org/10.48550/arXiv.2304.06592>.
