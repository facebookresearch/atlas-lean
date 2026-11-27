# Principal-component pseudo-exposures for time-varying effects

**Structural model.** For an exposure trajectory $X(t)$, $0 \le t \le T$, an outcome $Y$, and unmeasured confounder process $\vec U$,

$$Y = \beta_0 + \int_0^T \beta(t)\,X(t)\,dt + g_Y(\vec U, \epsilon_Y),$$

so that shifting the trajectory by a known $a(t)$ changes the mean outcome by $\int_0^T \beta(t) a(t)\,dt$. Discrete-time models are the special case $\beta(t) = \sum_k \beta_k\,\delta(t - t_k)$. With genetic instruments satisfying the usual relevance, independence and exclusion assumptions, summary statistics obey $\hat\theta_j = \int_0^T \beta(t)\,\hat\alpha_j(t)\,dt + \epsilon_j$, where $\hat\theta_j$ and $\hat\alpha_j(t)$ are the associations of instrument $j$ with the outcome and with the exposure at time $t$. If every $\alpha_j(t)$ is constant in $t$, only the cumulative effect $\int \beta$ is identified.

**Pseudo-exposures.** Write $X(t) = \mu(t) + \sum_{k=1}^K \xi_k \phi_k(t) + e(t)$, for example with $\phi_k$ the leading eigenfunctions of the functional principal component (Karhunen–Loève) expansion, orthonormal in $L^2[0,T]$, and $\xi_k$ the individual scores. Substituting,

$$Y_i = \beta_0^* + \sum_{k=1}^K \beta^*_k\,\xi_{k,i} + \epsilon_i, \qquad \beta^*_k = \int_0^T \beta(t)\,\phi_k(t)\,dt,$$

with $\epsilon_i$ absorbing $\int \beta(t) e_i(t)\,dt$ ("structural pleiotropy", negligible when $e$ is small or independent of the instruments). This is multivariable Mendelian randomization with exposures $\xi_1,\dots,\xi_K$.

**Estimation.** With mean-centred instruments $Z \in \mathbb{R}^J$, the continuously updating GMM estimator

$$\hat\beta^* = \arg\min_\beta\ \hat g(\beta)^{\mathsf T}\,\hat\Omega(\beta)^{-1}\,\hat g(\beta), \qquad \hat g(\beta) = \hat{\mathbb{E}}_n\bigl[Z(Y - \xi^{\mathsf T}\beta)\bigr],$$

satisfies, if $\operatorname{cov}(Z,\epsilon) = 0$ with homoskedastic errors and standard GMM regularity, $\sqrt n(\hat\beta^* - \beta^*) \to N\bigl(0, (G^{\mathsf T}\Omega(\beta^*)^{-1}G)^{-1}\bigr)$ with $G = \mathbb{E}(-Z\xi^{\mathsf T})$.

**Curve inversion.** Orthonormality gives the solution $\beta(t) = \phi(t)^{\mathsf T}\beta^*$ of $\beta^* = \int \phi\,\beta$, hence $\hat\beta(t) = \sum_k \phi_k(t)\hat\beta^*_k$ with pointwise standard error $\sqrt{\phi(t)^{\mathsf T}\hat\Sigma\,\phi(t)}$. Because this inverse problem is ill-posed (any function orthogonal to $\phi_1,\dots,\phi_K$ can be added), one may instead posit $\beta(t) = \sum_{l=1}^L \gamma_l b_l(t)$ for known basis functions; then $Y = \beta_0 + \sum_l \gamma_l \xi^*_l + \epsilon$ with transformed exposures $\xi^* = B^{\mathsf T}\xi$, $B = \int_0^T \phi(t) b(t)^{\mathsf T} dt \in \mathbb{R}^{K\times L}$, and $L \le K$ is needed to identify $\gamma$.

**Instrument strength over time.** Under the expansion, the genetic association with the exposure at time $t$ is $\alpha(t) \approx \sum_k \alpha_k \phi_k(t)$ with $\alpha_k$ the association with the $k$-th score, so time-varying instrument strength is assessed by conditional $F$-statistics for the scores. Nearly proportional $\alpha_j(t)$ across variants make the instruments conditionally weak, which motivates identification-robust (Lagrange multiplier) confidence sets.

## Expansion

The reduction trades an infinite-dimensional instrumental-variable problem for a $K$-dimensional one: genetic variation can only reveal the part of $\beta(t)$ lying in the span of the time patterns along which genes move the exposure. Using estimated principal components borrows strength across sparsely measured time points, avoiding noisy time-point-specific associations.

## Depends on

- [Ratio estimate of a single SNP](../ratio-estimate.md)
- [Linear moment model for instrumental variables](../linear-moment-model.md)

## Sources

- H. Tian, A. Patel, S. Burgess, "Estimating Time-Varying Exposure Effects Through Continuous-Time Modelling in Mendelian Randomization", Statistics in Medicine 43 (2024) 5166–5181, Equations (1)–(11) and Sections 2–3, <https://doi.org/10.1002/sim.10222>, PMCID PMC7616825.
