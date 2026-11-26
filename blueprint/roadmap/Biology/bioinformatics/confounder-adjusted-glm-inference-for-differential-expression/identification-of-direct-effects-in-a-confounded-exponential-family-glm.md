# Identification of direct effects in a confounded exponential-family GLM

**Model.** For $p$ genes, the expression vector $\mathbf{y} \in \mathbb{R}^p$ has conditionally independent entries from a regular one-parameter exponential family,

$$p(y_j \mid \theta_j) = h(y_j)\exp\big(y_j\theta_j - A(\theta_j)\big),$$

with $A$ strictly convex and three times continuously differentiable (Gaussian, Poisson, binomial and negative binomial with known dispersion are covered). The natural parameters depend linearly on observed covariates $\mathbf{x} \in \mathbb{R}^d$ (e.g. case/control status) and unmeasured confounders $\mathbf{z} \in \mathbb{R}^r$:

$$\boldsymbol{\theta} = \mathbf{B}\mathbf{x} + \boldsymbol{\Gamma}\mathbf{z}, \qquad \mathbf{B} \in \mathbb{R}^{p \times d},\ \boldsymbol{\Gamma} \in \mathbb{R}^{p \times r},$$

with $p \gg d, r$. Writing $\mathbf{D} = \mathbb{E}[\mathbf{z}\mathbf{x}^\top]\mathbb{E}[\mathbf{x}\mathbf{x}^\top]^{-1}$ and $\mathbf{w} = \mathbf{z} - \mathbf{D}\mathbf{x}$ gives $\boldsymbol{\theta} = (\mathbf{B} + \boldsymbol{\Gamma}\mathbf{D})\mathbf{x} + \boldsymbol{\Gamma}\mathbf{w}$: regressing on $\mathbf{x}$ alone recovers the confounded coefficient $\mathbf{B} + \boldsymbol{\Gamma}\mathbf{D}$, not the direct effect $\mathbf{B}$. Let $\boldsymbol{\Sigma}_w = \mathrm{Cov}(\mathbf{w})$ and $\mathcal{P}_{\boldsymbol\Gamma}$ the orthogonal projection onto the column space of $\boldsymbol{\Gamma}$.

**Proposition (identification of $\mathbf{B}$).** Suppose there is a sequence $\tau_p$ bounded away from zero with

$$\lambda_r(\boldsymbol{\Gamma}\boldsymbol{\Sigma}_w\boldsymbol{\Gamma}^\top) \ge \tau_p, \qquad \max_{j}(\boldsymbol{\Gamma}\boldsymbol{\Sigma}_w\boldsymbol{\Gamma}^\top)_{jj} = O(1), \qquad \max_{\ell \le d}\|\mathbf{B}_\ell\|_1 = o(\tau_p),$$

where $\mathbf{B}_\ell$ is the $\ell$-th column of $\mathbf{B}$. Then as $p \to \infty$, $\mathbf{B} = \mathcal{P}^\perp_{\boldsymbol\Gamma}\mathbf{B} + o(1)$ with $\|\mathcal{P}_{\boldsymbol\Gamma}\mathbf{B}\|_F \lesssim \sqrt{p}\,\|\mathbf{B}\|_{1,1}/\tau_p$, and both $\mathcal{P}_{\boldsymbol\Gamma}$ and $\mathbf{B}$ are asymptotically identified from the first two moments of $(\mathbf{x}, \mathbf{y})$.

**Estimation (GCATE).** From $n$ samples with $\boldsymbol{\Theta} = \mathbf{X}\mathbf{B}^\top + \mathbf{Z}\boldsymbol{\Gamma}^\top$: (1) fit the joint maximum likelihood $\hat{\boldsymbol\Theta}_0 = \mathbf{X}\hat{\mathbf{F}}^\top + \hat{\mathbf{W}}_0\hat{\boldsymbol\Gamma}_0^\top$ under $\mathcal{P}_{\mathbf{X}}\mathbf{W} = \mathbf{0}$; (2) take $\hat{\boldsymbol\Gamma} = \sqrt{p}\,\mathbf{V}\boldsymbol\Sigma^{1/2}$ from the SVD $\hat{\mathbf{W}}_0\hat{\boldsymbol\Gamma}_0^\top = \sqrt{np}\,\mathbf{U}\boldsymbol\Sigma\mathbf{V}^\top$; (3) solve the $\ell_1$-penalized likelihood in $(\mathbf{B}, \mathbf{Z})$ under $\mathcal{P}_{\hat{\boldsymbol\Gamma}}\mathbf{B} = \mathbf{0}$. Under sub-Gaussian covariates and latent factors, bounded parameters, $s$-sparse columns of $\mathbf{B}$ and $\lambda_r(p^{-1}\boldsymbol\Gamma\boldsymbol\Gamma^\top) \asymp 1$, any $\hat{\boldsymbol\Theta}_0$ with likelihood at least that of the truth has $\|\hat{\boldsymbol\Theta}_0 - \boldsymbol\Theta^*\|_F = O(\sqrt{(d+r)(n \vee p)})$ with high probability, and

$$\|\mathcal{P}_{\hat{\boldsymbol\Gamma}} - \mathcal{P}_{\boldsymbol\Gamma^*}\|_{\mathrm{op}} = O_P\big((n \wedge p)^{-1/2}\big).$$

## Expansion

If $\boldsymbol\Gamma$ were known, projecting $\boldsymbol\theta$ onto the orthogonal complement of its column space removes the confounder exactly: $\mathcal{P}^\perp_{\boldsymbol\Gamma}\boldsymbol\theta = \mathcal{P}^\perp_{\boldsymbol\Gamma}\mathbf{B}\mathbf{x}$. The column space is identified because $\boldsymbol\Gamma\boldsymbol\Sigma_w\boldsymbol\Gamma^\top$ is a rank-$r$ spiked component with eigenvalues at least $\tau_p$, and the sparsity condition makes the unrecoverable part $\mathcal{P}_{\boldsymbol\Gamma}\mathbf{B}$ negligible: a sparse vector has small projection onto a dense, well-spread $r$-dimensional subspace. With $\tau_p = p$ this recovers the Gaussian identification condition of the linear confounder-adjustment literature; here it holds for any exponential family, which covers count data from RNA-seq without a variance-stabilizing transform.

## Sources

- Jin-Hong Du, Larry Wasserman, Kathryn Roeder, "Simultaneous inference for generalized linear models with unmeasured confounders", arXiv:2309.07261 (2023): Section 2.1 (model and the proposition on identification of $\mathbf{B}$), Section 3 (GCATE algorithm; theorems on the estimation error of $\hat{\boldsymbol\Theta}_0$ and of $\mathcal{P}_{\hat{\boldsymbol\Gamma}}$). <https://doi.org/10.48550/arXiv.2309.07261>
