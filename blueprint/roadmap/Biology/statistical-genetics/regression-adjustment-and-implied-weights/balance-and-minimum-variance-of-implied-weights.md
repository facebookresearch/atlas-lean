# Exact balance and minimum dispersion of regression implied weights

With the notation of the [single-regression](uniregression-implied-weights.md) and [two-regression](multiregression-implied-weights.md) implied weights, write $w_i^{\mathrm{MRI}} = w_i^{\mathrm{MRI}}(\bar X)$ (the ATE weights) and

$$X^*_{\mathrm{URI}} = S_c(S_t+S_c)^{-1}\bar X_t + S_t(S_t+S_c)^{-1}\bar X_c, \qquad X^*_{\mathrm{MRI}} = \bar X.$$

**Proposition (Chattopadhyay and Zubizarreta, Proposition 3).** For estimation of the average treatment effect:

1. *Balance.* $\sum_{Z_i=1} w_i^{\mathrm{URI}} X_i = \sum_{Z_i=0} w_i^{\mathrm{URI}} X_i = X^*_{\mathrm{URI}}$ and $\sum_{Z_i=1} w_i^{\mathrm{MRI}} X_i = \sum_{Z_i=0} w_i^{\mathrm{MRI}} X_i = X^*_{\mathrm{MRI}}$.
2. *Representativeness.* The weighted covariate profiles are the vectors $X^*_{\mathrm{URI}}$ and $X^*_{\mathrm{MRI}}$ above; only MRI balances at the full-sample mean.
3. *Dispersion.* Within-group variances of the weights (mean squared deviation from $1/n_t$ or $1/n_c$) are
   $n^2 n_t^{-1} n_c^{-2}(\bar X-\bar X_t)^\top(S_t+S_c)^{-1}S_t(S_t+S_c)^{-1}(\bar X-\bar X_t)$ and $n^2 n_c^{-1} n_t^{-2}(\bar X-\bar X_c)^\top(S_t+S_c)^{-1}S_c(S_t+S_c)^{-1}(\bar X-\bar X_c)$ for URI, and $n_t^{-1}(\bar X-\bar X_t)^\top S_t^{-1}(\bar X-\bar X_t)$ and $n_c^{-1}(\bar X-\bar X_c)^\top S_c^{-1}(\bar X-\bar X_c)$ for MRI.
4. *Extrapolation.* Both sets of weights can be negative, so the estimators need not be sample bounded.
5. *Optimality.* In each group, the URI (respectively MRI) weights are the weights of minimum variance among all weights that sum to one and satisfy the balance constraint in item 1 with target $X^*_{\mathrm{URI}}$ (respectively $X^*_{\mathrm{MRI}}$).

Because $\bar X - \bar X_t = (n_c/n)(\bar X_c - \bar X_t)$, the dispersions are Mahalanobis-type distances between the group means: a better balanced sample yields less variable weights.

## Depends on

- [Implied weights of the single-regression treatment-effect estimator](uniregression-implied-weights.md)
- [Implied weights of two-regression imputation](multiregression-implied-weights.md)

## Expansion

Balance for MRI: $\sum_{Z_i=1} w_i^{\mathrm{MRI}}(x) X_i = \bar X_t + S_t S_t^{-1}(x - \bar X_t) = x$. The dispersion formulas follow by summing the squared correction terms, e.g. $\sum_{Z_i=1}\{(X_i-\bar X_t)^\top S_t^{-1}(\bar X-\bar X_t)\}^2 = (\bar X-\bar X_t)^\top S_t^{-1}(\bar X-\bar X_t)$. For optimality, minimizing $\sum w_i^2$ subject to $\sum w_i = 1$ and $\sum w_i X_i = x$ has Lagrangian stationarity $w_i = \lambda_0 + \lambda^\top X_i$, an affine function of $X_i$; the constraints then force exactly the implied weights. Negativity occurs once $\bar X$ is far enough from $\bar X_t$ relative to the spread of the $X_i$.

## Sources

- A. Chattopadhyay and J. R. Zubizarreta, *On the implied weights of linear regression for causal inference*, Biometrika (2023). <https://doi.org/10.1093/biomet/asac058>. Section 4.1, Proposition 3.
