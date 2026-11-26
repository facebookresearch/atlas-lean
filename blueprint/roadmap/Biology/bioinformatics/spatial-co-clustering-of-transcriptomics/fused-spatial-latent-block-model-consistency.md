# Fused spatial latent block model for co-clustering spatial transcriptomics

**Model.** A spatial transcriptomics matrix $X=(x_{ij})$ has $n$ spots (rows, with spatial neighborhoods $\mathcal N_i$) and $d$ genes (columns). Latent row labels $z_i\in[K_0]$ (tissue domains) and column labels $w_j\in[L_0]$ (gene modules) are independent, and given the labels

$$x_{ij}\mid(z_i=k,\,w_j=l)\sim N(\mu_{kl},\lambda_{kl})$$

independently (a Gaussian latent block model). Spatial coherence of domains is encoded by a Potts prior on the row labels,

$$p(\mathbf z)=C_\beta^{-1}\exp\Bigl\{\tfrac12\beta\sum_{i=1}^n\sum_{j\in\mathcal N_i}\mathbf 1(z_i=z_j)\Bigr\},\qquad\beta\ge0 .$$

**Three-step estimator.** (I) Variational EM with over-specified numbers of clusters $K\ge K_0$, $L\ge L_0$ and mean-field posteriors $s_{ik}\approx P(z_i=k)$, $t_{jl}\approx P(w_j=l)$; the iterates converge to a stationary point of the variational objective. (II) *Penalized fusion*: with the posteriors fixed, minimize the weighted Gaussian criterion plus

$$\gamma_{nd}\Bigl[\sum_{k_1<k_2}w^{(r)}_{k_1k_2}\|\boldsymbol\mu_{k_1\cdot}-\boldsymbol\mu_{k_2\cdot}\|+\sum_{l_1<l_2}w^{(c)}_{l_1l_2}\|\boldsymbol\mu_{\cdot l_1}-\boldsymbol\mu_{\cdot l_2}\|\Bigr],\qquad w^{(r)}_{k_1k_2}=\frac{\sqrt L}{\|\hat{\boldsymbol\mu}_{k_1\cdot}-\hat{\boldsymbol\mu}_{k_2\cdot}\|},\ w^{(c)}_{l_1l_2}=\frac{\sqrt K}{\|\hat{\boldsymbol\mu}_{\cdot l_1}-\hat{\boldsymbol\mu}_{\cdot l_2}\|},$$

by ADMM, so that redundant row or column clusters merge; (III) spatial smoothing of spot labels with the Potts prior, $\beta$ estimated by maximum pseudo-likelihood.

**Theorem.** Assume the true parameters lie in a compact set away from the boundary, $\boldsymbol\mu^*$ is identifiable up to joint label permutations, and $n,d\to\infty$ with $\ln d=o(n)$ and $\ln n=o(d)$ (conditions (C1)–(C3)). Let $M$ be the generalized misclassification rate (over surjective label maps from fitted to true clusters).

1. *(Over-fitted VEM.)* For every $\delta>0$, $\hat M=o_p((nd)^{-\delta})$; every fitted row and column cluster has a non-vanishing fraction of spots and genes, and the fitted means of clusters mapped to the same true cluster converge to its true mean.
2. *(Fusion recovers the numbers of clusters.)* If $nd\,\gamma_{nd}\to\infty$ and $\sqrt{nd}\,\gamma_{nd}\to0$, then $P(\tilde K=K_0,\ \tilde L=L_0)\to1$ and $\tilde M=o_p((nd)^{-\delta})$ for every $\delta>0$.
3. *(Benefit of the spatial prior.)* In the disordered phase of the Potts model with homoscedastic blocks, the spot-level error probability of the spatially smoothed rule satisfies

$$\frac{\mathbb P_s\{\hat z_i\ne z_i^*\}}{\mathbb P\{\hat z_i\ne z_i^*\}}\le\Bigl(\frac{2e^{\beta/2}+K-2}{e^\beta+K-1}\Bigr)^{|\mathcal N_i|}+o(1),$$

which decreases in $\beta$ and in the neighborhood size.

## Expansion

In the over-fitted latent block model, each spot carries $d$ conditionally independent observations, so the posterior of its row label concentrates exponentially fast in $d$ (and that of each gene in $n$); this gives the superpolynomial misclassification rate. Spurious clusters are then copies of true clusters with asymptotically equal mean profiles, so adaptive group-fusion penalties, large for nearly identical centers and negligible for distinct ones, merge exactly the redundant clusters, in the same way as adaptive lasso oracle properties. The Potts factor multiplies the local prior odds of the neighborhood-majority label by up to $e^{\beta}$ per agreeing neighbor, giving the per-neighbor contraction factor in item 3.

## Sources

- B. Cai, Y. Chen, K. Fang, X. Lin, "Fused Spatial Latent Block Models for Co-Clustering", arXiv:2606.04495 (2026), Section 2 (model and Potts prior), Section 3 (VEM, Proposition 3.1, penalized fusion and spatial smoothing) and Section 4 (Definition 4.1, Conditions (C1)–(C3), Theorems 4.1–4.2, Proposition 4.1). <https://doi.org/10.48550/arXiv.2606.04495>
