# Implied weights of the single-regression treatment-effect estimator

Let units $i = 1, \dots, n$ carry a treatment indicator $Z_i \in \{0,1\}$, a covariate vector $X_i \in \mathbb{R}^k$ and an observed outcome $Y_i^{\mathrm{obs}}$. Put $n_t = \sum_i Z_i$, $n_c = n - n_t$, group means $\bar X_t = n_t^{-1}\sum_{i:Z_i=1} X_i$, $\bar X_c = n_c^{-1}\sum_{i:Z_i=0} X_i$, pooled mean $\bar X = n^{-1}(n_t \bar X_t + n_c \bar X_c)$, and scaled within-group covariance matrices

$$S_t = \sum_{i:Z_i=1}(X_i-\bar X_t)(X_i-\bar X_t)^\top, \qquad S_c = \sum_{i:Z_i=0}(X_i-\bar X_c)(X_i-\bar X_c)^\top,$$

both assumed invertible. Let $\hat\tau^{\mathrm{OLS}}$ be the ordinary least squares coefficient of $Z_i$ in the regression of $Y_i^{\mathrm{obs}}$ on $(1, X_i, Z_i)$ (uniregression imputation, URI).

**Proposition (Chattopadhyay and Zubizarreta, Proposition 1).**

$$\hat\tau^{\mathrm{OLS}} = \sum_{i:Z_i=1} w_i^{\mathrm{URI}} Y_i^{\mathrm{obs}} - \sum_{i:Z_i=0} w_i^{\mathrm{URI}} Y_i^{\mathrm{obs}},$$

where

$$w_i^{\mathrm{URI}} = \frac{1}{n_t} + \frac{n}{n_c}(X_i-\bar X_t)^\top (S_t+S_c)^{-1}(\bar X - \bar X_t) \quad (Z_i = 1),$$

$$w_i^{\mathrm{URI}} = \frac{1}{n_c} + \frac{n}{n_t}(X_i-\bar X_c)^\top (S_t+S_c)^{-1}(\bar X - \bar X_c) \quad (Z_i = 0),$$

and the weights sum to one within each group: $\sum_{i:Z_i=1} w_i^{\mathrm{URI}} = \sum_{i:Z_i=0} w_i^{\mathrm{URI}} = 1$.

So the regression coefficient is a difference of Hájek (self-normalized) weighted means, and the weights depend on $(Z_i, X_i)$ only, never on the outcomes. They are uniform exactly when $\bar X_t = \bar X_c$, and they may be negative. The paper also notes $w_i^{\mathrm{URI}} = w_i^{\mathrm{MRI}}(x^*)$ with $x^* = S_c(S_t+S_c)^{-1}\bar X_t + S_t(S_t+S_c)^{-1}\bar X_c$, where $w^{\mathrm{MRI}}$ are the two-regression implied weights.

## Expansion

By the Frisch–Waugh–Lovell theorem, $\hat\tau^{\mathrm{OLS}}$ is a linear functional of $Y^{\mathrm{obs}}$ with coefficients built from the residual of $Z$ regressed on $(1, X)$, so some outcome-free weights exist. To identify them, check that the displayed weights sum to one in each group (the correction term is a centered sum) and balance the covariates: using $\bar X - \bar X_t = (n_c/n)(\bar X_c - \bar X_t)$ one gets $\sum_{Z_i=1} w_i^{\mathrm{URI}} X_i = \bar X_t + S_t(S_t+S_c)^{-1}(\bar X_c - \bar X_t) = x^*$, and symmetrically for controls. These are the normal equations of the fitted model, which pin down the coefficient of $Z$.

## Sources

- A. Chattopadhyay and J. R. Zubizarreta, *On the implied weights of linear regression for causal inference*, Biometrika (2023). <https://doi.org/10.1093/biomet/asac058>. Section 3, Proposition 1.
