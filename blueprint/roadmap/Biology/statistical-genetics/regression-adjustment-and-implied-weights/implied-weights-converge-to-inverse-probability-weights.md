# Regression implied weights as inverse probability weights, and multiple robustness

Let $(X_i, Z_i, Y_i(0), Y_i(1))$, $i = 1, \dots, n$, be independent draws with $Y_i^{\mathrm{obs}} = Y_i(Z_i)$, unconfoundedness and overlap, propensity score $e(x) = \Pr(Z_i = 1 \mid X_i = x)$, and outcome regressions $m_z(x) = E\{Y_i(z) \mid X_i = x\}$. Let $w_x^{\mathrm{MRI}}$ denote the [two-regression implied weight](multiregression-implied-weights.md) for the ATE of a unit with covariate vector $x$.

**Theorem 1 (Chattopadhyay and Zubizarreta).**

1. For treated units, $n\,w_x^{\mathrm{MRI}} \to 1/e(x)$ in probability for all $x \in \operatorname{supp}(X_i)$ if and only if the propensity score is inverse linear, $e(x) = 1/(\alpha_0 + \alpha_1^\top x)$ with $\alpha_0 \in \mathbb{R}$, $\alpha_1 \in \mathbb{R}^k$. If moreover $\sup_{x \in \operatorname{supp}(X_i)}\|x\|_2 < \infty$, the convergence is uniform: $\sup_x |n\,w_x^{\mathrm{MRI}} - 1/e(x)| \to 0$ in probability.
2. For control units, $n\,w_x^{\mathrm{MRI}} \to 1/\{1-e(x)\}$ pointwise if and only if $1 - e(x)$ is inverse linear, uniformly under the same boundedness condition.

**Theorem 2 (Chattopadhyay and Zubizarreta).** The MRI estimator $\sum_{Z_i=1} w_i^{\mathrm{MRI}} Y_i^{\mathrm{obs}} - \sum_{Z_i=0} w_i^{\mathrm{MRI}} Y_i^{\mathrm{obs}}$ is consistent for the ATE if any one of the following holds:

- (i) $m_0$ is linear and $e$ is inverse linear;
- (ii) $m_1$ is linear and $1 - e$ is inverse linear;
- (iii) $m_1$ and $m_0$ are linear;
- (iv) $e$ is constant;
- (v) $m_1 - m_0$ is constant, $e$ is linear, and $p^2\operatorname{var}(X_i \mid Z_i=1) = (1-p)^2\operatorname{var}(X_i \mid Z_i=0)$, where $p$ is the probability limit of $n_t/n$.

Since $e$ and $1 - e$ cannot both be inverse linear unless $e$ is constant, the treated and control regressions implicitly posit different propensity models, and the two sets of MRI weights converge to their true inverse probability weights simultaneously only when $e$ is constant.

## Depends on

- [Implied weights of two-regression imputation](multiregression-implied-weights.md)

## Expansion

For a treated unit, $n\,w_x^{\mathrm{MRI}} = n/n_t + n(x - \bar X_t)^\top S_t^{-1}(\bar X - \bar X_t)$ converges to an affine function of $x$, so its limit can equal $1/e(x)$ only if $1/e$ is affine; conversely, when $1/e$ is affine, the balancing property of inverse probability weights identifies the limit with $1/e(x)$. Uniformity follows from the affine form once $x$ ranges over a bounded set. In Theorem 2, under (i) the treated weights behave like inverse probability weights, so the treated weighted mean is consistent for $E\{Y_i(1)\}$ whatever $m_1$ is, while the control regression is consistent because $m_0$ is linear; (ii) is symmetric, (iv) makes both arms behave like a randomized experiment, (iii) is standard OLS consistency, and (v) uses an asymptotic equivalence between MRI and URI.

## Sources

- A. Chattopadhyay and J. R. Zubizarreta, *On the implied weights of linear regression for causal inference*, Biometrika (2023). <https://doi.org/10.1093/biomet/asac058>. Section 4.2, Theorems 1 and 2.
