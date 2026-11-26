# Focused instrument selection with locally invalid instruments

Let $p$ uncorrelated variants have population associations $\beta_{X_j}$ with a risk factor and $\beta_{Y_j}$ with an outcome satisfying $\beta_{Y} = \beta_X\theta_0 + \tau$, where $\tau_j$ is the direct (pleiotropic) effect of variant $j$. Assume two-sample summary data $\hat\beta_{X_j} \sim N(\beta_{X_j}, \sigma_{X_j}^2)$, $\hat\beta_{Y_j} \sim N(\beta_{Y_j}, \sigma_{Y_j}^2)$, mutually uncorrelated, with known variances of orders $1/n_X$ and $1/n_Y$; a known core set $S_0$ (growing proportionally with $p$) with $\tau_j = 0$ for $j \in S_0$; many weak instruments ($\|\beta_X\|_2 = O(1)$, $\|\beta_X\|_3/\|\beta_{X,0}\|_2 \to 0$, $p/(n\|\beta_{X,0}\|_2^2) = O(1)$); and locally invalid additional instruments, $\|\tau\|_2^2 = O(1/n)$. Write $S$ for the additional variants and

$$\Omega_j = \sigma_{Y_j}^2 + \theta_0^2\sigma_{X_j}^2,\quad \eta_C = \sum_{j\in S_0}\frac{\beta_{X_j}^2}{\Omega_j},\quad \zeta_C = \sum_{j\in S_0}\frac{\sigma_{X_j}^2\sigma_{Y_j}^2}{\Omega_j^2},$$

with $\eta_S, \zeta_S$ the same sums over $S$. The Core and Full estimators minimize the profile objective $\sum_j (\hat\beta_{Y_j} - \hat\beta_{X_j}\theta)^2/(\sigma_{Y_j}^2 + \sigma_{X_j}^2\theta^2)$ over $j \in S_0$ and over $j \in S_0 \cup S$, respectively.

1. The Core estimator satisfies $\Delta_C^{-1/2}(\hat\theta_C - \theta_0) \to N(0,1)$ with $\Delta_C = \eta_C^{-2}(\eta_C + \zeta_C)$.
2. The Full estimator is consistent, and $\Delta_F^{-1/2}(\hat\theta_F - \theta_0 - b) \to N(0,1)$ with

$$\Delta_F = \frac{\eta_C + \eta_S + \zeta_C + \zeta_S}{(\eta_C + \eta_S)^2},\qquad b = \frac{1}{\eta_C + \eta_S}\sum_{j\in S}\frac{\beta_{X_j}\tau_j}{\Omega_j}.$$

The squared bias and the variance are of the same order, so including $S$ trades variance for bias.

3. With $\hat\Omega_j$, $\hat\eta_C$, $\hat\eta_S$ computed by plugging in $\hat\theta_C$ and $\hat\beta_{X_j}^2 - \sigma_{X_j}^2$, the estimator $\hat b = (\hat\eta_C + \hat\eta_S)^{-1}\left[\sum_{j\in S}\hat\Omega_j^{-1}\hat\beta_{X_j}\hat\beta_{Y_j} - \hat\theta_C\sum_{j\in S}\hat\Omega_j^{-1}(\hat\beta_{X_j}^2 - \sigma_{X_j}^2)\right]$ is asymptotically unbiased but not consistent: $\Delta_B^{-1/2}(\hat b - b) \to N(0,1)$ with

$$\Delta_B = (\eta_C + \eta_S)^{-2}\left[\eta_S + \zeta_S + \xi_S + \eta_C^{-2}\eta_S^2(\eta_C + \zeta_C)\right],\qquad \xi_S = 2\theta_0^2\sum_{j\in S}\frac{\sigma_{X_j}^4}{\Omega_j^2}.$$

The Focused estimator selects $\hat\theta_F$ when $\hat W = \max(\hat b^2 - \hat\Delta_B, 0) + \hat\Delta_F - \hat\Delta_C \le 0$ and $\hat\theta_C$ otherwise; it is consistent, but because the selection criterion is not consistently estimated, valid confidence intervals must account for selection.

## Depends on

- [Ratio estimate](../ratio-estimate.md)

## Expansion

Each variant's Wald ratio $\hat\beta_{Y_j}/\hat\beta_{X_j}$ estimates $\theta_0 + \tau_j/\beta_{X_j}$, and the LIML objective weights these by their inverse variances, so invalid instruments in $S$ shift the Full estimator by the weighted average $b$ of their direct effects. Under local misspecification this shift is of the same order as the sampling error, which is what makes a mean-squared-error comparison meaningful. The extra variance terms $\zeta$ come from many weak instruments; omitting them would understate the Full estimator's variance and bias the selection toward including invalid variants. Subtracting $\hat\Delta_B$ from $\hat b^2$ removes the leading bias of the squared-bias estimate, as in focused moment selection.

## Sources

- A. Patel, F. J. DiTraglia, V. Zuber and S. Burgess, "Selecting invalid instruments to improve Mendelian randomization with two-sample summary data", *Annals of Applied Statistics* (2024), Section 2, Assumptions 1–4 and Eq. (3), and Section 3, Theorems 1 and 2. <https://doi.org/10.1214/23-aoas1856> (PMC7615940)
