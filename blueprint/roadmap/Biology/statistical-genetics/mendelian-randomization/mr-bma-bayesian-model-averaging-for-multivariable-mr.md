# MR-BMA: Bayesian model averaging for multivariable Mendelian randomization

**Data and model.** For genetic variants $i = 1, \dots, n$ (independent instruments) and candidate risk factors $1, \dots, d$, let $\beta^\star_{Y_i}$ be the variant–outcome association with standard error $\operatorname{se}(\beta^\star_{Y_i})$ and $\beta^\star_{X_{ij}}$ the variant–risk-factor associations, from two independent samples. Standardize $\beta_{Y_i} = \beta^\star_{Y_i}/\operatorname{se}(\beta^\star_{Y_i})$ and $\beta_{X_{ij}} = \beta^\star_{X_{ij}}/\operatorname{se}(\beta^\star_{Y_i})$. Multivariable MR is the weighted regression

$$\beta_Y \mid \beta_X, \theta, \tau \sim \mathcal{N}\!\left(\beta_X\theta, \tfrac{1}{\tau} I\right),$$

whose coefficients $\theta_j$ are the direct causal effects of the risk factors. A model $M_\gamma$, $\gamma \in \{0,1\}^d$, includes the risk factors with $\gamma_j = 1$, with conjugate priors $\theta_\gamma \sim \mathcal{N}(0, \nu_\gamma/\tau)$ ($\nu_\gamma$ diagonal) and $\tau \sim \Gamma(\kappa/2, \lambda/2)$.

**Bayes factor and posterior.** With $\Omega = (\nu_\gamma^{-1} + \beta_{X_\gamma}^\top\beta_{X_\gamma})^{-1}$ and $\Theta = \Omega\beta_{X_\gamma}^\top\beta_Y$,

$$\mathrm{BF}(M_\gamma) = \frac{|\Omega|^{1/2}}{|\nu_\gamma|^{1/2}}\left(\frac{\beta_Y^\top\beta_Y - \Theta^\top\Omega^{-1}\Theta}{\beta_Y^\top\beta_Y}\right)^{-n/2}.$$

With independent inclusion probability $p$, $p(M_\gamma) = p^{k}(1-p)^{d-k}$ for $k = |\gamma|$, and

$$\mathrm{PP}(M_\gamma \mid \beta_Y, \beta_X) = \frac{p(M_\gamma)\mathrm{BF}(M_\gamma)}{\sum_{\gamma'} p(M_{\gamma'})\mathrm{BF}(M_{\gamma'})}, \qquad \mathrm{MIP}(j) = \sum_{\gamma:\,\gamma_j = 1}\mathrm{PP}(M_\gamma \mid \beta_Y, \beta_X).$$

The model-averaged causal effect is $\hat\theta_{\mathrm{MACE}}(j) = \sum_{\gamma:\,\gamma_j=1}\mathrm{PP}(M_\gamma)\,\hat\theta_\gamma(j)$ with the posterior-mean (ridge-type) estimate $\hat\theta_\gamma = \Omega\beta_{X_\gamma}^\top\beta_Y$.

## Remarks

Standardizing by $\operatorname{se}(\beta^\star_{Y_i})$ turns the inverse-variance-weighted regression of [IVW Mendelian randomization](ivw.md) into an ordinary regression with unit error variance, so a standard conjugate normal–gamma variable-selection model applies and its marginal likelihood is available in closed form. Ranking risk factors by marginal inclusion probability rather than by a single best model handles strongly correlated candidates (for example lipid subfractions): when two correlated risk factors explain the same signal, models containing both get little evidence, and the MIP splits between them. The posterior is computed exactly by enumeration for small $d$ and by a shotgun stochastic search over high-probability models otherwise. Outlying or influential variants, which signal pleiotropy not mediated by the measured risk factors, are flagged by each variant's contribution $q_i$ to Cochran's $Q$ and by Cook's distance in the best models.

## Sources

- V. Zuber, J. M. Colijn, C. Klaver and S. Burgess, "Selecting likely causal risk factors from high-throughput experiments using multivariable Mendelian randomization", Nature Communications 11 (2020), 29, Methods (Equations (1)–(15)), <https://doi.org/10.1038/s41467-019-13870-3>, PMCID PMC6946691.
