# Regression adjustment in completely randomized experiments with many covariates

**Setting (finite-population randomization model).** Units $i = 1,\dots,n$ have fixed potential outcomes $Y_i(1), Y_i(0)$ and covariates $x_i \in \mathbb R^p$; the covariate matrix $X = (x_1,\dots,x_n)^\top$ is centered ($\mathbf 1^\top X = 0$) with rank $p$. A completely random set $T_1$ of $n_1$ units is treated ([complete randomization](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md)), the other $n_0 = n - n_1$ units ($T_0$) are controls, and the only randomness is the treatment assignment. The target is the [average treatment effect](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md) $\tau = n^{-1}\sum_i\{Y_i(1) - Y_i(0)\} = \mu_1 - \mu_0$.

Let $(\mu_t, \beta_t) = \big(n^{-1}\sum_i Y_i(t),\ (X^\top X)^{-1}X^\top Y(t)\big)$ be the population least-squares coefficients of $Y(t)$ on $(\mathbf 1, X)$, $e(t) = Y(t) - \mu_t\mathbf 1 - X\beta_t$ the potential residuals, $H = X(X^\top X)^{-1}X^\top$ and $\kappa = \max_i H_{ii} \in [p/n, 1]$ the maximum leverage.

**Estimator.** For $t \in \{0,1\}$ regress the observed outcomes of arm $t$ on $(1, X_t)$ with intercept $\hat\mu_t$; set $\hat\tau_{\mathrm{adj}} = \hat\mu_1 - \hat\mu_0$ (equivalent to the treatment coefficient in the fully interacted regression of Lin). The asymptotic variance is

$$\sigma_n^2 = n_1^{-1}\sum_{i=1}^n e_i^2(1) + n_0^{-1}\sum_{i=1}^n e_i^2(0) - n^{-1}\sum_{i=1}^n\{e_i(1) - e_i(0)\}^2 .$$

**Assumptions.** (A1) $n/n_1 = O(1)$, $n/n_0 = O(1)$; (A2) $\kappa\log p = o(1)$; (A3) the correlation of $e(1)$ and $e(0)$ exceeds $-1+\eta$ for a fixed $\eta > 0$; (A4) $E_\infty^2/(nE_2) = o(1)$, where $E_2 = n^{-1}\max\{\|e(0)\|_2^2, \|e(1)\|_2^2\}$ and $E_\infty = \max\{\|e(0)\|_\infty, \|e(1)\|_\infty\}$.

**Theorem (expansion and consistency).** Under (A1)–(A2), with $\hat\tau_e = n_1^{-1}\sum_{i\in T_1}e_i(1) - n_0^{-1}\sum_{i\in T_0}e_i(0)$ (mean $0$; with $\sigma_n^2$ as defined above its exact variance is $\sigma_n^2/(n-1)$, by Neyman's formula with population variances of divisor $n - 1$, and $\sigma_n^2/n$ asymptotically) and $\Delta = \max_t |n^{-1}\sum_i e_i(t)H_{ii}|$,

$$\hat\tau_{\mathrm{adj}} - \tau = \hat\tau_e + O_P\Big(\Delta + \big[E_2(\kappa^2 p\log p + \kappa)/n\big]^{1/2}\Big),$$

and $\hat\tau_{\mathrm{adj}}$ is consistent if $E_2 = o\{n/(\kappa p + 1)\}$; in particular for fixed $p$ with $E_2 = o(n)$, or diverging $p$ with $E_2 = O(n/p)$.

**Theorem (asymptotic normality).** Under (A1)–(A4), $n^{1/2}(\hat\tau_{\mathrm{adj}} - \tau)/\sigma_n \Rightarrow N(0,1)$ if $\kappa^2 p\log p = o(1)$ and $n\Delta^2 = o(E_2)$; a sufficient condition is $\kappa p = o(1)$, which for $\kappa = O(p/n)$ means $p = o(n^{1/2})$. A debiased estimator $\hat\tau^{\mathrm{de}}_{\mathrm{adj}}$, which subtracts the plug-in leading bias built from $\hat\Delta_t = n_t^{-1}\sum_{i\in T_t}\hat e_iH_{ii}$, satisfies $n^{1/2}(\hat\tau^{\mathrm{de}}_{\mathrm{adj}} - \tau)/\sigma_n \Rightarrow N(0,1)$ under (A1)–(A4) and only $\kappa^2p\log p = o(1)$, i.e. $p = o\{n^{2/3}/(\log n)^{1/3}\}$ when $\kappa = O(p/n)$. The HC0–HC3 variance estimators $\hat\sigma^2_{\mathrm{HC}j}$ are asymptotically conservative: $\hat\sigma^2_{\mathrm{HC}j}/\sigma_n^2 \ge 1 - o_P(1)$.

## Depends on

- [Expectation of a statistic under complete randomization](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md)
- [Finite-population average treatment effect](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md)

## Proof depends on

- [Variance of the difference in means under complete randomization](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp-sq-diff-in-means-sub-ate.md)

## Expansion

By the normal equations $\mathbf 1^\top e(t) = 0$ and $X^\top e(t) = 0$, $\hat\mu_t - \mu_t$ equals the arm-$t$ mean of $e(t)$ minus a correction from the in-sample regression of $e(t)$ on $X_t$; the correction's bias is driven by leverage-weighted residuals ($\Delta_t$) and its fluctuation by matrix concentration for sampling without replacement, which is where $\kappa$ and $p\log p$ enter. The leading term $\hat\tau_e$ is a difference in means of fixed numbers and obeys [Neyman's variance formula](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp-sq-diff-in-means-sub-ate.md) and Hájek's finite-population central limit theorem under (A4).

## Sources

- Lihua Lei and Peng Ding, "Regression adjustment in completely randomized experiments with a diverging number of covariates", Biometrika (2020), <https://doi.org/10.1093/biomet/asaa103>. arXiv:1806.07585. Section 2 (Eqs. (1)–(10)); Assumptions 1–4; Theorems 1–5 and Corollary 1.
