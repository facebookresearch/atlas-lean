# Multivariable Mendelian randomization: summary-data likelihood and direct effects

**Model.** Let $X_1, \dots, X_K$ be risk factors and $Y$ an outcome with

$$Y = \sum_{k=1}^K \beta_k X_k + (\text{confounding}) + \varepsilon_Y,$$

and let $G_1, \dots, G_J$ be uncorrelated genetic variants that are (i) associated with at least one risk factor, (ii) independent of the confounders, and (iii) associated with $Y$ only through the risk factors. For variant $j$, univariable regressions give estimates $\hat X_{kj}$ (standard error $\sigma_{X_kj}$) of the variant–risk-factor associations and $\hat Y_j$ (standard error $\sigma_{Yj}$) of the variant–outcome association.

**Likelihood.** The summary-data model assumes, independently over $j$,

$$\begin{pmatrix}\hat X_{1j}\\ \vdots \\ \hat X_{Kj}\\ \hat Y_j\end{pmatrix} \sim \mathcal N_{K+1}\!\left(\begin{pmatrix}\xi_{1j}\\ \vdots\\ \xi_{Kj}\\ \sum_{k}\beta_k\,\xi_{kj}\end{pmatrix},\ \Sigma_j\right),$$

where $\Sigma_j$ has diagonal entries $\sigma_{X_1j}^2, \dots, \sigma_{X_Kj}^2, \sigma_{Yj}^2$ and off-diagonal entries $\rho\,\sigma\sigma'$ built from correlations $\rho_{kl}, \rho_{kY}$ between the estimates (zero when the associations come from non-overlapping samples). The model has $K(J+1)$ parameters ($\xi_{kj}$ and $\beta_k$), and $\beta$ is estimated by maximizing the product likelihood or by Bayesian methods. For variants in linkage disequilibrium with known correlations, the $J$ separate $(K+1)$-variate normals are replaced by one $J(K+1)$-variate normal whose between-variant correlations equal the variant correlations.

**Interpretation.** Each $\beta_k$ is the **direct** causal effect of $X_k$ on $Y$, not mediated by the other included risk factors. If $X_3$ also causes $X_1$ with coefficient $\alpha$, the total effect of $X_3$ is $\beta_3 + \alpha\beta_1$, and the multivariable estimate of $\beta_3$ does not recover it: in the paper's simulation $\beta_3 = -0.1$, $\alpha = 0.5$, $\beta_1 = 0.3$, so the total effect is $+0.05$ while the estimates are centred near $-0.1$.

## Expansion

The mean vector says that the outcome association of a variant is the $\beta$-weighted sum of its risk-factor associations, which is exactly instrument validity in a linear model. Writing $\Xi = (\xi_{kj})$ as a $J \times K$ matrix, the mean of $(\hat Y_1, \dots, \hat Y_J)$ is $\Xi\beta$, so $\beta$ is identifiable from the means only when $\Xi$ has rank $K$: every risk factor needs genetic variation not explained by the others. Because the model conditions on all included risk factors, paths $X_3 \to X_1 \to Y$ are blocked, which is why the parameters are direct effects. In simulation the likelihood method and individual-level 2SLS had similar efficiency, while the ad hoc two-step residual regression method was biased and underpowered; with weak instruments the multivariable estimates inherit weak-instrument bias toward the observational association (overlapping samples) or the null (separate samples).

## Sources

- S. Burgess and S. G. Thompson, "Multivariable Mendelian randomization: the use of pleiotropic genetic variants to estimate causal effects", American Journal of Epidemiology (2015), Methods, Equation (1), and Simulation Study, Equation (2) and Table 2, <https://doi.org/10.1093/aje/kwu283> (PMC4325677).
