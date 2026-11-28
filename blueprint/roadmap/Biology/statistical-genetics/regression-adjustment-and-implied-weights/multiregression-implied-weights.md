# Implied weights of two-regression imputation

Use the notation of the [single-regression implied weights](uniregression-implied-weights.md): treatment indicators $Z_i \in \{0,1\}$, covariates $X_i \in \mathbb{R}^k$, outcomes $Y_i^{\mathrm{obs}}$, group sizes $n_t, n_c$, group means $\bar X_t, \bar X_c$, pooled mean $\bar X$ and invertible scaled covariance matrices $S_t, S_c$. Multi-regression imputation (MRI) fits separate OLS models $Y_i^{\mathrm{obs}} = \beta_{0t} + \beta_{1t}^\top X_i + \epsilon_{it}$ on treated units and $Y_i^{\mathrm{obs}} = \beta_{0c} + \beta_{1c}^\top X_i + \epsilon_{ic}$ on controls, and imputes $\hat m_1, \hat m_0$ from them. For $x \in \mathbb{R}^k$ define

$$w_i^{\mathrm{MRI}}(x) = \frac{1}{n_t} + (X_i - \bar X_t)^\top S_t^{-1}(x - \bar X_t) \quad (Z_i=1), \qquad w_i^{\mathrm{MRI}}(x) = \frac{1}{n_c} + (X_i - \bar X_c)^\top S_c^{-1}(x - \bar X_c) \quad (Z_i=0).$$

**Proposition (Chattopadhyay and Zubizarreta, Proposition 2).** The MRI estimators are

- $\widehat{\mathrm{ATE}} = \sum_{i:Z_i=1} w_i^{\mathrm{MRI}}(\bar X) Y_i^{\mathrm{obs}} - \sum_{i:Z_i=0} w_i^{\mathrm{MRI}}(\bar X) Y_i^{\mathrm{obs}}$,
- $\widehat{\mathrm{ATT}} = \bar Y_t - \sum_{i:Z_i=0} w_i^{\mathrm{MRI}}(\bar X_t) Y_i^{\mathrm{obs}}$,
- $\widehat{\mathrm{CATE}}(x^*) = \sum_{i:Z_i=1} w_i^{\mathrm{MRI}}(x^*) Y_i^{\mathrm{obs}} - \sum_{i:Z_i=0} w_i^{\mathrm{MRI}}(x^*) Y_i^{\mathrm{obs}}$,

and $\sum_{i:Z_i=1} w_i^{\mathrm{MRI}}(x) = \sum_{i:Z_i=0} w_i^{\mathrm{MRI}}(x) = 1$ for every $x \in \mathbb{R}^k$.

As with the single regression, the weights are outcome-free and so belong to the design stage of a study. If $n_t S_t = n_c S_c$ the URI weights coincide with $w^{\mathrm{MRI}}(\bar X)$.

## Depends on

- [Implied weights of the single-regression treatment-effect estimator](uniregression-implied-weights.md)

## Expansion

Within the treated group the fitted value at $x$ is $\hat m_1(x) = \bar Y_t + (x - \bar X_t)^\top S_t^{-1}\sum_{Z_i=1}(X_i - \bar X_t)Y_i^{\mathrm{obs}}$, which is $\sum_{Z_i=1} w_i^{\mathrm{MRI}}(x) Y_i^{\mathrm{obs}}$. The same holds for controls. Averaging $\hat m_1 - \hat m_0$ over the sample is evaluation at $\bar X$ by linearity, giving the ATE form; averaging over treated units gives evaluation at $\bar X_t$ and, since $\hat m_1(X_i)$ averages to $\bar Y_t$ there, the ATT form.

## Sources

- A. Chattopadhyay and J. R. Zubizarreta, *On the implied weights of linear regression for causal inference*, Biometrika (2023). <https://doi.org/10.1093/biomet/asac058>. Section 3, Proposition 2.
