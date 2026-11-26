# Bayesian sparse linear mixed model (BSLMM) and the PVE/PGE parameterization

For $n$ individuals with phenotypes $y \in \mathbb R^n$, genotypes $X \in \mathbb R^{n\times p}$ (centered) and a known relatedness matrix $K$, the **BSLMM** is

$$y = \mathbf 1_n\mu + X\tilde\beta + u + \epsilon, \qquad u \sim \mathrm{MVN}_n(0, \sigma_b^2\tau^{-1}K), \qquad \epsilon \sim \mathrm{MVN}_n(0, \tau^{-1}I_n),$$

$$\tilde\beta_i \overset{\text{iid}}{\sim} \pi\,N(0, \sigma_a^2\tau^{-1}) + (1-\pi)\,\delta_0 ,$$

with sparse effects $\tilde\beta$, a polygenic random effect $u$, residual precision $\tau$ and sparsity $\pi \in (0,1]$.

**Special cases.** If $K = p^{-1}XX^\top$, then $u \overset{d}{=} Xb$ with $b_i \overset{\text{iid}}{\sim} N(0, \sigma_b^2/(p\tau))$, so the model is the linear regression $y = \mathbf 1\mu + X\beta + \epsilon$ with the two-normal mixture prior

$$\beta_i \sim \pi\,N\big(0, \sigma_a^2\tau^{-1} + \sigma_b^2(p\tau)^{-1}\big) + (1-\pi)\,N\big(0, \sigma_b^2(p\tau)^{-1}\big).$$

Setting $\pi = 0$ (no sparse effects) gives the LMM/ridge regression (BLUP); setting $\sigma_b = 0$ gives Bayesian variable selection regression with a point-normal prior.

**PVE and PGE.** With $V(x) = n^{-1}\sum_i(x_i - \bar x)^2$,

$$\mathrm{PVE} = \frac{V(X\tilde\beta + u)}{V(X\tilde\beta + u) + \tau^{-1}}, \qquad \mathrm{PGE} = \frac{V(X\tilde\beta)}{V(X\tilde\beta + u)},$$

called the proportion of phenotypic variance explained by all genetic terms and the proportion of genetic variance explained by the sparse effects. $\mathrm{PVE} \in [0, 1)$ for $\tau > 0$, but $\mathrm{PGE}$ is defined only when $V(X\tilde\beta + u) > 0$ and is not a share on every draw: $X\tilde\beta$ and $u$ can be negatively correlated across individuals, and for a nonconstant $a = X\tilde\beta$ and $u = -a/2$ one gets $\mathrm{PGE} = V(a)/V(a/2) = 4$. It lies in $[0, 1]$ when, for example, the sample covariance of $X\tilde\beta$ and $u$ is nonnegative. Priors are placed through the approximations

$$h = \frac{p\pi s_a\sigma_a^2 + s_b\sigma_b^2}{p\pi s_a\sigma_a^2 + s_b\sigma_b^2 + 1}, \qquad \rho = \frac{p\pi s_a\sigma_a^2}{p\pi s_a\sigma_a^2 + s_b\sigma_b^2},$$

where $s_a = (np)^{-1}\sum_{i,j}x_{ij}^2$ is the average genotype variance and $s_b = n^{-1}\sum_i k_{ii}$; the default priors are $h \sim U(0,1)$, $\rho \sim U(0,1)$ and $\log\pi \sim U(\log(1/p), 0)$, with $\rho = 0$ the LMM and $\rho = 1$ BVSR.

## Depends on

- [BLUP as a conditional law](cond-distrib-mixed-model.md)

## Proof depends on

- [Linear images of multivariate Gaussians](../../../Probability/distributions/continuous/gaussian-conditioning/map-to-euclidean-lin-multivariate-gaussi.md)

## Expansion

$\mathbb E[\tilde\beta^\top X^\top X\tilde\beta/n] = p\pi s_a\sigma_a^2\tau^{-1}$ (expected number $p\pi$ of causal markers, each with variance $\sigma_a^2/\tau$, times the average genotype variance) and $\mathbb E[u^\top u/n] = s_b\sigma_b^2\tau^{-1}$; $h$ and $\rho$ are ratios of these expectations, hence approximations to the expected PVE and PGE. The marginal likelihood of $y$ given $(h, \rho, \pi)$ and the inclusion indicators is available in closed form after integrating out $(\tilde\beta, u, \tau)$, which the paper samples by Metropolis–Hastings.

## Sources

- Xiang Zhou, Peter S. Carbonetto and Matthew Stephens, "Polygenic Modeling with Bayesian Sparse Linear Mixed Models", PLoS Genetics (2013), <https://doi.org/10.1371/journal.pgen.1003264> (PMC3567190). Methods, Eqs. (1)–(23).
