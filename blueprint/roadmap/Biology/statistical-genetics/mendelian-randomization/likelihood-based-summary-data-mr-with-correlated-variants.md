# Likelihood-based summary-data Mendelian randomization with correlated variants

Let $X_k$ and $Y_k$ $(k = 1, \dots, K)$ be published estimates of the associations of variant $k$ with a risk factor and with an outcome, with standard errors $\sigma_{Xk}$ and $\sigma_{Yk}$, and let $\rho_{ij}$ be the correlation between variants $i$ and $j$ ($\rho_{ii} = 1$). The likelihood-based method models the true variant–risk-factor associations $\xi = (\xi_1, \dots, \xi_K)$ as nuisance parameters and the causal effect $\beta_L$ through:

1. **Uncorrelated variants, non-overlapping samples.** $X_k \sim \mathcal N(\xi_k, \sigma_{Xk}^2)$ and $Y_k \sim \mathcal N(\beta_L\xi_k, \sigma_{Yk}^2)$, all independent.
2. **Correlated variants.** $X \sim \mathcal N_K(\xi, \Sigma_X)$ and $Y \sim \mathcal N_K(\beta_L\xi, \Sigma_Y)$ independently, with

$$(\Sigma_X)_{ij} = \sigma_{Xi}\sigma_{Xj}\rho_{ij}, \qquad (\Sigma_Y)_{ij} = \sigma_{Yi}\sigma_{Yj}\rho_{ij}.$$

3. **Overlapping samples.** $(X, Y) \sim \mathcal N_{2K}\!\left(\begin{pmatrix}\xi\\ \beta_L\xi\end{pmatrix}, \begin{pmatrix}\Sigma_X & \Sigma_{XY}\\ \Sigma_{YX} & \Sigma_Y\end{pmatrix}\right)$ with $(\Sigma_{XY})_{ij} = \theta\,\sigma_{Xi}\sigma_{Yj}\rho_{ij}$ and $\Sigma_{YX} = \Sigma_{XY}^\top$, where $\theta$ is the correlation between the two association estimates.

Estimates of $\beta_L$ follow by maximizing the likelihood (or by Bayesian methods). In model 1, if the $X_k$ are treated as exact ($\sigma_{Xk} \to 0$, so $\xi_k = X_k$), the maximum likelihood estimate of $\beta_L$ is the inverse-variance-weighted estimate

$$\hat\beta_{\mathrm{IVW}} = \frac{\sum_k X_k Y_k \sigma_{Yk}^{-2}}{\sum_k X_k^2 \sigma_{Yk}^{-2}}.$$

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)
- [IVW estimator minimizes the weighted residual sum of squares](ivw-le-weighted-ssr.md)

## Expansion

With $\xi = X$ fixed, the log-likelihood in $\beta_L$ is $-\frac12\sum_k (Y_k - \beta_L X_k)^2/\sigma_{Yk}^2$ up to constants, a weighted least-squares problem through the origin whose solution is the IVW ratio. Keeping $\xi$ free propagates the uncertainty in $X_k$, which is why the likelihood method gives wider, better-calibrated intervals when the risk-factor associations are imprecise, while the IVW standard error $\big(\sum_k X_k^2\sigma_{Yk}^{-2}\big)^{-1/2}$ is over-precise. Correlated variants enter only through the off-diagonal covariances; ignoring them overstates precision.

## Sources

- S. Burgess, R. A. Scott, N. J. Timpson, G. Davey Smith, S. G. Thompson, EPIC-InterAct Consortium, "Using published data in Mendelian randomization: a blueprint for efficient identification of causal risk factors", European Journal of Epidemiology 30 (2015), 543–552, <https://doi.org/10.1007/s10654-015-0011-z> (PMC4516908). Equations (1)–(5).
