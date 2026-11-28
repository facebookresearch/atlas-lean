# Efficiency bound and augmented calibration weighting for trial generalization

Use the setting and Assumptions 1-4 of [calibration weighting for trial generalizability](calibration-weighting-for-trial-generalizability.md), with outcome means $\mu_{a,1}(X) = E(Y \mid X, A = a, \delta = 1)$, so that $\tau(X) = \mu_{1,1}(X) - \mu_{0,1}(X)$, and residuals $\Delta_a = Y - \mu_{a,1}(X)$.

**Theorem 2 (semiparametric efficiency bound).** Under Assumptions 1-4 the efficient score for $\tau_0$ is

$$\phi(X, A, Y, \delta, \tilde\delta) = \frac{\delta}{\pi_\delta(X)}\Big\{\frac{A\Delta_1}{\pi_A} - \frac{(1-A)\Delta_0}{1-\pi_A}\Big\} + \tilde\delta d\{\tau(X) - \tau_0\} \qquad\text{(eq. 7)}$$

and the efficiency bound is

$$V_{\mathrm{eff}} = E\Big[\frac{\delta}{\pi_\delta(X)^2}\Big\{\frac{V\{Y(1) \mid X, \delta\}}{\pi_A} + \frac{V\{Y(0) \mid X, \delta\}}{1-\pi_A}\Big\} + \tilde\delta d^2\{\tau(X) - \tau_0\}^2\Big]. \qquad\text{(eq. 8)}$$

**Augmented calibration weighting estimator (eq. 9).** With calibration weights $\hat q_i$ (which exist with a finite multiplier only when the target mean $\tilde g$ lies in the relative interior of the convex hull of the trial values $g(X_i)$, assumed to hold with probability tending to one in Theorems 3 and 4) and fitted outcome models $\mu_{a,1}(X;\hat\beta_a)$, $\hat\Delta_{a,i} = Y_i - \mu_{a,1}(X_i;\hat\beta_a)$,

$$\hat\tau_{\mathrm{ACW}} = \sum_{i=1}^N \delta_i\hat q_i\Big\{\frac{A_i\hat\Delta_{1,i}}{\pi_{A_i}} - \frac{(1-A_i)\hat\Delta_{0,i}}{1-\pi_{A_i}}\Big\} + \Big(\sum_{i=1}^N\tilde\delta_i d_i\Big)^{-1}\sum_{i=1}^N\tilde\delta_i d_i\{\mu_{1,1}(X_i;\hat\beta_1) - \mu_{0,1}(X_i;\hat\beta_0)\}.$$

**Theorem 3 (double robustness and local efficiency).** Under Assumptions 1-4, if either the linear-CATE Assumption 5 or the log-linear sampling-score Assumption 6 holds, $\hat\tau_{\mathrm{ACW}}$ is consistent for $\tau_0$; if both hold, $N^{1/2}(\hat\tau_{\mathrm{ACW}} - \tau_0) \to N(0, V_{\mathrm{eff}})$ in distribution.

**Theorem 4 (flexible nuisance models).** Under Assumptions 1-4, let $\pi_\delta(X;\hat\eta)$ and $\mu_{a,1}(X;\hat\beta_a)$ be general semiparametric fits with (C1) $\|\pi_\delta(X;\hat\eta) - \pi_\delta(X)\| = o_p(1)$ and $\|\mu_{a,1}(X;\hat\beta_a) - \mu_{a,1}(X)\| = o_p(1)$, and (C2) $\|\pi_\delta(X;\hat\eta) - \pi_\delta(X)\|\sum_{a=0}^1\|\mu_{a,1}(X;\hat\beta_a) - \mu_{a,1}(X)\| = o_p(n^{-1/2})$, in $L_2(P)$ norm. Then $\hat\tau_{\mathrm{ACW}}$ is consistent and attains $V_{\mathrm{eff}}$.

**Lemma 1 (which covariates to calibrate).** Let $X_C$ be the confounders (affecting both trial participation and outcome), $X_O$ the outcome predictors, meaning all covariates predictive of the outcome, so that $X_O$ contains $X_C$ and $\pi_\delta(X_O) = \pi_\delta(X_C)$, and $X_I$ the instruments, which affect trial participation but not the outcome given $X_C$, so that $V\{Y(a) \mid X_C, X_I\} = V\{Y(a) \mid X_C\}$; all are subsets of the basis $g(X)$, and $X_{C+I} = X_C \cup X_I$. Then the first term of $V_{\mathrm{eff}}$ computed with $X^*$,

$$V_1^* = E\Big[\frac{\delta}{\pi_\delta(X^*)^2}\Big\{\frac{V\{Y(1) \mid X^*, \delta\}}{\pi_A} + \frac{V\{Y(0) \mid X^*, \delta\}}{1-\pi_A}\Big\}\Big], \qquad * \in \{C, O, C+I\},$$

satisfies $V_1^O \le V_1^C \le V_1^{C+I}$. Here $X_O$ is the full set of outcome predictors, confounders included, as in the proof (Web Appendix C.5, which starts from $\pi_\delta(X^O) = \pi_\delta(X^C)$ and $V\{Y(a) \mid X^O\} \le V\{Y(a) \mid X^C\}$) and in the simulation (Web Appendix E.1, where the outcome predictors $X_3, X_4, X_5$ include $X_3$, which also enters the sampling score); if $X_O$ omitted the confounders, that first step $\pi_\delta(X^O) = \pi_\delta(X^C)$ would fail.

## Expansion

The efficient score has a trial part (an inverse-sampling-weighted, augmented IPW residual) and an observational part (the design-weighted deviation of the CATE). $\hat\tau_{\mathrm{ACW}}$ is the plug-in solution of its sample version, with the calibration weights standing in for $1/\pi_\delta$. Its error contains the product of sampling-score and outcome-model errors, giving double robustness and the product-rate condition (C2). Lemma 1 says to balance outcome predictors and avoid instruments of trial participation, which only inflate $1/\pi_\delta^2$.

## Depends on

- [Calibration weighting to generalize a randomized trial to a target population](calibration-weighting-for-trial-generalizability.md)

## Sources

- D. Lee, S. Yang, L. Dong, X. Wang, D. Zeng and J. Cai, *Improving trial generalizability using observational studies*, Biometrics (2023). <https://doi.org/10.1111/biom.13609> (PMCID: PMC9166225)
