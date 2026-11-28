# Debiased inference for direct effects in a confounded GLM

**Setting.** Work in the [confounded exponential-family GLM](identification-of-direct-effects-in-a-confounded-exponential-family-glm.md) $\boldsymbol\Theta = \mathbf{X}\mathbf{B}^\top + \mathbf{Z}\boldsymbol\Gamma^\top$ for an $n \times p$ expression matrix, with initial estimates $(\hat{\mathbf{B}}, \hat{\mathbf{Z}}, \hat{\boldsymbol\Gamma})$ from the projected, $\ell_1$-penalized joint likelihood and $\hat{\boldsymbol\theta}_i = \hat{\mathbf{B}}\mathbf{x}_i + \hat{\boldsymbol\Gamma}\hat{\mathbf{z}}_i$. To test the first covariate's effect $b_{j1}$ on gene $j$, define the one-step corrected estimator

$$\hat b^{\mathrm{de}}_{j1} = \hat b_{j1} + \hat{\mathbf{u}}^\top \frac{1}{n}\sum_{i=1}^n \mathbf{x}_i\big(\mathbf{y}_i - A'(\hat{\boldsymbol\theta}_i)\big)^\top \mathbf{v}_i, \qquad \mathbf{v}_i = \hat\omega_i\,\mathrm{diag}\big(A''(\hat{\boldsymbol\theta}_i)\big)^{-1}\mathcal{P}^\perp_{\hat{\boldsymbol\Gamma}}\mathbf{e}_j,$$

where $\hat{\mathbf{u}}$ minimizes $\mathbf{u}^\top\big(\frac1n\sum_i\hat\omega_i\mathbf{x}_i\mathbf{x}_i^\top\big)\mathbf{u}$ subject to $\|\frac1n\sum_i\hat\omega_i\mathbf{x}_i\mathbf{x}_i^\top\mathbf{u} - \mathbf{e}_1\|_\infty \le \lambda_n$ and $\max_i|\mathbf{x}_i^\top\mathbf{u}| \le \tau_n$, with $\lambda_n \asymp \sqrt{\log(nd)/n}$, $\tau_n \asymp \sqrt{\log n}$. The variance proxy is $\hat\sigma_j^2 = \hat{\mathbf{u}}^\top\frac1n\sum_i\hat\omega_i\mathbf{x}_i\mathbf{x}_i^\top\hat{\mathbf{u}}$.

**Theorem (asymptotic normality).** Assume the conditions under which $\|\hat{\mathbf{B}} - \mathbf{B}^*\|_F = O_P(r_{n,p})$ and $\|\hat{\mathbf{B}} - \mathbf{B}^*\|_{1,1} = O_P(r'_{n,p})$ (bounded natural parameters, $s$-sparse columns of $\mathbf{B}^*$, sub-Gaussian covariates and latent factors, spiked loadings, eigenvalue-gap identifiability of the latent factors, and $\|\mathcal{P}_{\boldsymbol\Gamma^*}\mathbf{B}^*\|_{1,1} = O(p^{k/2}\|\mathcal{P}_{\boldsymbol\Gamma^*}\mathbf{B}^*\|_F)$ for some $k \in [0,1)$). Suppose further that (i) $n/\log(nd) = o(p^{3/2})$ and $n = o(p^{2(1-k)})$, and (ii) $\hat\omega_i = \omega(\mathbf{x}_i, \mathbf{z}_i^*, \mathcal{D}_2)$ for a function $\omega$ bounded away from $0$ and $\infty$, where $\mathcal{D}_2$ is an independent half of the sample used to fit $(\hat{\mathbf{B}}, \hat{\boldsymbol\Gamma})$. Then for each $j$, as $n, p \to \infty$,

$$\sqrt{n}\,\frac{\hat b^{\mathrm{de}}_{j1} - b^*_{j1}}{\sigma_j} \Rightarrow \mathcal{N}(0,1),$$

and the choice $\hat\omega_i = A''(\hat\theta_{ij})$ makes $\hat\sigma_j$ consistent for $\sigma_j$.

**Proposition (simultaneous inference).** Let $t_j = \sqrt{n}(\hat b^{\mathrm{de}}_{j1} - b^*_{j1})/\hat\sigma_j$ and $\mathcal{N}_p = \{j : b^*_{j1} = 0\}$. Under the same assumptions, as $n, p, |\mathcal{N}_p| \to \infty$,

$$\frac{1}{|\mathcal{N}_p|}\sum_{j \in \mathcal{N}_p}\mathbf{1}\{|t_j| > z_{\alpha/2}\} \xrightarrow{P} \alpha, \qquad \limsup\ \mathbb{P}\Big(\sum_{j \in \mathcal{N}_p}\mathbf{1}\{|t_j| > z_{\alpha/(2p)}\} \ge 1\Big) \le \alpha,$$

so per-gene tests have asymptotic level $\alpha$ on average over null genes and Bonferroni controls the family-wise error rate.

## Depends on

- [Identification of direct effects in a confounded exponential-family GLM](identification-of-direct-effects-in-a-confounded-exponential-family-glm.md)

## Expansion

A Taylor expansion of $A'$ at $\hat\theta_{ij}$ splits the residual $\mathbf{y}_i - A'(\hat{\boldsymbol\theta}_i)$ into stochastic error, a remaining bias linear in $\hat{\boldsymbol\theta}_i - \boldsymbol\theta^*_i$, and a quadratic remainder. The projection $\mathcal{P}^\perp_{\hat{\boldsymbol\Gamma}}$ annihilates the confounder part of the bias, the constraint on $\hat{\mathbf{u}}$ cancels the bias in $\mathbf{b}_j$ up to $\lambda_n\|\hat{\mathbf{b}}_j - \mathbf{b}^*_j\|_1$, and condition (i) makes the quadratic remainder $o_P(n^{-1/2})$; the central limit theorem then applies to the stochastic term. The many-gene regime is a blessing here: estimation errors scale with $(n \wedge p)^{-1/2}$, so more genes than samples is what makes the confounders removable. Without confounders the estimator reduces to the usual one-step score correction of a GLM, and for Gaussian outcomes with unit weights to the classical debiased lasso.

## Sources

- Jin-Hong Du, Larry Wasserman, Kathryn Roeder, "Simultaneous inference for generalized linear models with unmeasured confounders", arXiv:2309.07261 (2023): Section 3.3 (theorem on the estimation error of $\hat{\mathbf{B}}$), Section 4.1 (debiased estimator, optimization problem for $\hat{\mathbf{u}}$, theorem on asymptotic normality), Section 4.2 (proposition on simultaneous inference); applied to differential expression in a lupus single-cell cohort (Section 6). <https://doi.org/10.48550/arXiv.2309.07261>
