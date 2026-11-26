# Path-specific causal effects in a confounded multiscale gene-network model

**Model.** For subjects $i=1,\dots,N$, genes $j=1,\dots,p$ and cells $c$, observed single-cell expression is

$$x_{ijc}=m_{ij}+\boldsymbol\rho_j^\top\mathbf v_{ic}+\boldsymbol\alpha_j^\top\mathbf f_{ic}+\delta_{ijc},$$

where $m_{ij}$ is the latent subject-level expression, $\mathbf v_{ic}$ measured and $\mathbf f_{ic}$ unmeasured cell-level factors, and $\delta_{ijc}$ measurement error. Latent expression follows a linear structural equation model on a DAG $\mathcal G$,

$$\mathbf M=\mathbf 1\boldsymbol\mu^\top+\mathbf Z\boldsymbol\Gamma+\mathbf U\boldsymbol\Lambda+\mathbf M\mathbf B+\mathbf E,$$

with measured subject covariates $\mathbf Z$, unmeasured confounders $\mathbf U$, structural noise $\mathbf E$, and $\mathbf B$ upper-triangular in a topological order ($B_{jk}\ne0$ only for edges $j\to k$). A phenotype obeys $y_i=\mu_y+\mathbf m_i^\top\boldsymbol\beta_m+\mathbf z_i^\top\boldsymbol\beta_z+\mathbf u_i^\top\boldsymbol\beta_u+\varepsilon_{yi}$.

**Path and total effects.** For a directed path $\pi=(j_1,\dots,j_k,y)$ from gene $j_1$ through genes $j_2,\dots,j_k$ to the phenotype,

$$\mathrm{PCE}_\pi=\Bigl(\prod_{l=1}^{k-1}B_{j_l,j_{l+1}}\Bigr)\beta_{m,j_k},\qquad \mathrm{TCE}_j=\bigl\{(\mathbf I-\mathbf B)^{-1}\bigr\}_{[j,:]}\boldsymbol\beta_m=\sum_{\pi\in\Pi_{j\to y}}\mathrm{PCE}_\pi,$$

so the total causal effect of gene $j$ decomposes exactly into the effects transmitted along each regulatory path (Wright's path-tracing rule in matrix form).

**Theorem (residual factorization).** Let $\bar{\mathbf X}$ be subject-averaged expression, let $\mathbf Z_{\mathrm{aug}}$ collect the measured subject covariates and averaged cell covariates, and let $\mathbf R=(\mathbf I-\mathbf P_{[\mathbf 1,\mathbf Z_{\mathrm{aug}}]})\bar{\mathbf X}$. If the stacked confounder loadings satisfy $\mathrm{rank}(\boldsymbol\Lambda_{\mathrm{aug}})=m+r$ (subject confounders $\mathbf U$ together with averaged cell factors $\bar{\mathbf f}_i$), then

$$\mathbf R=\tilde{\mathbf U}_{\mathrm{aug}}\boldsymbol\Lambda_{\mathrm{aug}}(\mathbf I-\mathbf B)^{-1}+\tilde{\mathbf E}(\mathbf I-\mathbf B)^{-1}+\tilde{\boldsymbol\Delta},$$

where tildes denote projection off $[\mathbf 1,\mathbf Z_{\mathrm{aug}}]$ and $\tilde{\boldsymbol\Delta}$ is averaged measurement error. Since $(\mathbf I-\mathbf B)^{-1}$ is invertible, $\mathbf R$ is a rank-$(m+r)$ factor model plus noise, so, when $\|(\mathbf I-\mathbf B)^{-1}\|_2$ is bounded and the confounding signal $\boldsymbol\Phi=\tilde{\mathbf U}_{\mathrm{aug}}\boldsymbol\Lambda_{\mathrm{aug}}(\mathbf I-\mathbf B)^{-1}$ satisfies $\sigma_{m+r}(\boldsymbol\Phi)\gg\sqrt N+\sqrt p$, the confounder column space is recovered asymptotically by the top $m+r$ principal components of $\mathbf R$ (surrogate variables) without knowing $\mathbf B$; cell-level factors are recovered analogously from within-subject residuals. With the recovered surrogates and errors-in-variables corrections, the network and gene-outcome effects, and hence every $\mathrm{PCE}_\pi$ and $\mathrm{TCE}_j$, are estimated consistently with high-dimensional rates and support recovery, when ancestral relations learned from perturbation screens constrain the topology.

## Expansion

1. Solving the SEM gives $\mathbf M=(\mathbf 1\boldsymbol\mu^\top+\mathbf Z\boldsymbol\Gamma+\mathbf U\boldsymbol\Lambda+\mathbf E)(\mathbf I-\mathbf B)^{-1}$; substituting into the outcome model shows that a unit intervention on $m_j$ changes $y$ by $\{(\mathbf I-\mathbf B)^{-1}\}_{[j,:]}\boldsymbol\beta_m$, and expanding $(\mathbf I-\mathbf B)^{-1}=\sum_{t\ge0}\mathbf B^t$ (finite since $\mathbf B$ is nilpotent) enumerates directed paths.
2. Averaging the cell model over cells and projecting off measured covariates removes the intercept and measured effects, leaving confounders multiplied by the invertible network propagator, which gives the factorization.
3. Averaged measurement error biases naive regressions toward zero; an errors-in-variables correction subtracts its estimated covariance before solving for $\mathbf B$ and $\boldsymbol\beta_m$.

## Sources

- K. Park, H. Li, *Causal path analysis from perturbational and population-scale single-cell data with multiscale confounding and measurement error*, arXiv:2609.16510 (Propositions 1–3, Theorems 1–6, Corollaries 1 and 2). <https://doi.org/10.48550/arXiv.2609.16510>
