# Proxy–instrumental identification of causal parents in Perturb-seq

In the log-linear Perturb-seq structural equation model $\log\mu_j = \theta_{j0} + \sum_{k\in\mathrm{pa}(j)}\theta_{jk}\log\mu_k + \tau_jD_j + \beta_j^\top X + \gamma_j^\top U + \epsilon_j$ with Poisson-type counts $Y_j$ at depth $\ell$, let $\mathbf D = (D_1,\dots,D_p)$ and define the *link proxy* of $\log\mu_k$

$$\eta_k(\mathbf D,X) = \log\mathbb{E}[Y_k/\ell \mid \mathbf D,X,\ell].$$

**Theorem 2.** Assume either (A1) $U = \beta_{0u} + B_u^\top X + \epsilon_u$ with $\epsilon_u \perp X$, or (A1') $U \perp X$. Then for every gene $j$ and every $k \in \mathrm{anc}(j)$ the coefficient $\theta_{jk}$ is identified by quasi-maximum likelihood with mean function

$$\log\mathbb{E}[Y_j \mid \mathbf D,X,\ell] = \log\ell + \theta^*_{j0} + \beta_j^{*\top}X + \tau_jD_j + \sum_{k \in \mathrm{anc}(j)}\theta_{jk}\,\eta_k(\mathbf D,X),$$

with $\theta_{jk} = 0$ for $k \notin \mathrm{pa}(j)$. Hence every parent set $\mathrm{pa}(j)$, and the DAG, is identifiable.

**Two-stage estimator.** By induction over the DAG, $\eta_k(\mathbf D,X) = (1, D_k, \mathbf D_{\mathrm{anc}(k)}^\top, X^\top)\,\xi_k$ is linear, so (i) the first stage fits a GLM of $Y_k$ on $(D_k,\mathbf D_{\widehat{\mathrm{anc}}(k)},X)$ with offset $\log\ell$ to get $\hat\eta_k$; (ii) the second stage fits a GLM of $Y_j$ on $(X, D_j, \hat\eta_k : k \in \widehat{\mathrm{anc}}(j))$ with offset $\log\ell$. With the Murphy–Topel correction for estimated regressors, $z_{\theta_{jk}} = \hat\theta_{jk}/\sqrt{\hat V_{\mathrm{MT},kk}} \to N(0,1)$, and parents are selected by Wald tests under online FDR control.

## Depends on

- [Identifiability of ancestors and descendants under single-gene perturbations](identifiability-of-ancestors-and-descendants-under-single-gene-perturbations.md)

## Expansion

The perturbation indicators of the ancestors, $\mathbf D_{\mathrm{anc}(j)}$, act as instruments for the regulators of gene $j$: they are independent of $U$ given $X$, have no direct path to $\mu_j$ (exclusion), and move each $\mu_k$ (relevance, from $\tau_k \neq 0$). Replacing the confounded regressor $\log\mu_k$ by its projection on instruments and covariates removes the dependence on $U$; assumption (A1) or (A1') ensures that the part of $\gamma_j^\top U$ explained by $X$ is absorbed into $\beta^*_j$ and the intercept, while the residual is independent of the regressors. The procedure is the count-data analogue of two-stage least squares, with the GLM log link playing the role of the linear projection. The DAG search starts from sink nodes and moves toward roots, so the assembled graph is acyclic even when individual parent tests err.

## Sources

- Kwangmoon Park, Hongzhe Li, "Confounder-robust causal discovery and inference in Perturb-seq using proxy and instrumental variables", Journal of the American Statistical Association (2026), 1–44, <https://doi.org/10.1080/01621459.2026.2749694>. Published version of arXiv:2601.01830, cited next; locators there refer to the arXiv version.
- Kwangmoon Park and Hongzhe Li, *Confounder-robust causal discovery and inference in Perturb-seq using proxy and instrumental variables*, arXiv:2601.01830 (2026). <https://doi.org/10.48550/arXiv.2601.01830> Section 3 (Theorem 2) and Section 4.2 (first- and second-stage regressions, Murphy–Topel standard errors, online FDR parent selection).
