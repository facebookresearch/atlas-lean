# Calibration weighting to generalize a randomized trial to a target population

Let $X \in \mathbb{R}^p$ be covariates, $A \in \{0,1\}$ treatment and $Y$ outcome, with potential outcomes $Y(a)$, CATE $\tau(X) = E\{Y(1) - Y(0) \mid X\}$ and target-population ATE $\tau_0 = E\{\tau(X)\}$. A randomized trial (indicator $\delta = 1$) is drawn from the target population by an unknown mechanism with **sampling score** $\pi_\delta(X) = P(\delta = 1 \mid X)$; an observational sample (indicator $\tilde\delta = 1$) is drawn by a known design with weights $d = 1/P(\tilde\delta = 1 \mid X)$. Within the trial the treatment propensity $\pi_A(X) = P(A = 1 \mid X, \delta = 1)$ is known.

**Identification (Assumptions 1-3).** (1) $Y = AY(1) + (1-A)Y(0)$; (2) $\{Y(0), Y(1)\} \perp A \mid (X, \delta = 1)$ and $0 < \pi_A(X) < 1$; (3) $E\{Y(1) - Y(0) \mid X, \delta = 1\} = \tau(X)$ and $\pi_\delta(X) > 0$ almost surely. Then $\tau_0 = E\{\tau(X)\}$ is identified even though $f(X \mid \delta = 1) \ne f(X)$.

**Calibration weights (eqs. 2-5).** For chosen covariate functions $g(X)$, let $\tilde g = \sum_i \tilde\delta_i d_i g(X_i)/\sum_i \tilde\delta_i d_i$ be the design-weighted mean from the observational sample. Choose weights $q_i \ge 0$ on the $n$ trial units minimizing $\sum_i q_i\log q_i$ subject to $\sum_i q_i = 1$ and the balancing constraint $\sum_{i:\delta_i=1} q_i g(X_i) = \tilde g$. Such weights exist if and only if $\tilde g$ lies in the convex hull of $\{g(X_i) : \delta_i = 1\}$; positivity of $\pi_\delta$ in the population does not ensure this in a sample (if every trial unit has $g(X_i) = 0$ and $\tilde g = 1$, no weights balance). If $\tilde g$ lies in the **relative interior** of that convex hull, the solution has all $\hat q_i > 0$ and is given by a finite multiplier $\hat\lambda$,

$$\hat q_i = \frac{\exp\{\hat\lambda^{\top}g(X_i)\}}{\sum_{j=1}^n\exp\{\hat\lambda^{\top}g(X_j)\}}, \qquad \sum_{i=1}^n \exp\{\lambda^{\top}g(X_i)\}\{g(X_i) - \tilde g\} = 0 \text{ at } \lambda = \hat\lambda.$$

(the sums run over the $n$ trial units). If $\tilde g$ lies on the relative boundary of the hull, the entropy problem still has a unique solution, but some weights are zero and no finite $\hat\lambda$ represents it; the estimator below is defined only when feasible weights exist.

**Calibration-weighting estimator (eq. 6).**

$$\hat\tau_{\mathrm{CW}} = \sum_{i=1}^n \hat q_i\Big\{\frac{A_iY_i}{\pi_{A_i}} - \frac{(1-A_i)Y_i}{1 - \pi_{A_i}}\Big\}.$$

**Theorem 1 (double robustness).** Assume Assumptions 1-3, that the design-weighted mean $\hat\mu_g$ of $g(X)$ is root-$m$ asymptotically normal in the observational sample size $m$ (Assumption 4), and that, with probability tending to one, $\tilde g$ lies in the relative interior of the convex hull of the trial values $g(X_i)$, so that the weights exist with a finite multiplier. If either

- the CATE is linear in the calibration functions, $\tau(X) = \gamma_0^{\top}g(X)$ (Assumption 5), or
- the sampling score is log-linear, $\pi_\delta(X) = \exp\{\eta_0^{\top}g(X)\}$ (Assumption 6),

then $\hat\tau_{\mathrm{CW}}$ is consistent for $\tau_0$.

## Expansion

Balancing enforces the population identity $E[\{\pi_\delta(X)\}^{-1}\delta\,g(X)]/E[\{\pi_\delta(X)\}^{-1}\delta] = E\{g(X)\}$ (eq. 1) in sample. If $\tau$ is linear in $g$, the weighted IPW contrast has conditional mean $\sum_i \hat q_i\tau(X_i) = \gamma_0^{\top}\tilde g \to \tau_0$ regardless of how the trial was sampled. If instead $\pi_\delta$ is log-linear in $g$, the source shows a direct correspondence between the exponential-tilting weights $q(X_i;\hat\lambda)$ and normalized inverse sampling scores $1/\pi_\delta(X_i)$, so $\hat\tau_{\mathrm{CW}}$ is an inverse-probability-of-sampling-weighted estimator. Neither the sampling score nor the outcome means need to be modelled explicitly.

## Sources

- D. Lee, S. Yang, L. Dong, X. Wang, D. Zeng and J. Cai, *Improving trial generalizability using observational studies*, Biometrics (2023). <https://doi.org/10.1111/biom.13609> (PMCID: PMC9166225)
