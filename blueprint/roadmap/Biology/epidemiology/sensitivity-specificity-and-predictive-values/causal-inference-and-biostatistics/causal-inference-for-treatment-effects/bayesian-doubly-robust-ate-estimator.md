# Doubly robust average treatment effect from posterior draws of the nuisance models

Observe i.i.d. $D_i = (X_i, T_i, Y_i)$, $i = 1, \dots, n$, with $X_i \in \mathbb{R}^p$ ($p$ possibly larger than $n$), binary treatment $T_i$, and outcome $Y_i = Y_i(T_i)$ (SUTVA). Assume **unconfoundedness** $T \perp Y(t) \mid X$ for $t = 0, 1$ and **positivity** $\delta < P(T = 1 \mid X) < 1 - \delta$ for some $\delta \in (0,1)$. The target is $\Delta^* = E\{Y(1) - Y(0)\}$.

Let $\Psi$ collect the parameters of a propensity model $p_{ti} = P(T_i = t \mid X_i)$ and an outcome model $m_{ti} = E(Y_i \mid T_i = t, X_i)$. The augmented inverse-probability-weighted (doubly robust) estimating function (eq. 1) is

$$\Delta(D, \Psi) = \frac1n\sum_{i=1}^n\Big[\frac{T_iY_i - (T_i - p_{1i})m_{1i}}{p_{1i}} - \frac{(1-T_i)Y_i + (T_i - p_{1i})m_{0i}}{p_{0i}}\Big], \qquad p_{0i} = 1 - p_{1i}.$$

**Estimator (eq. 2).** Given posterior draws $\Psi^{(1)}, \dots, \Psi^{(B)}$ from $[\Psi \mid D]$,

$$\hat\Delta = E_{\Psi \mid D}[\Delta(D, \Psi)] \approx \frac1B\sum_{b=1}^B \Delta(D, \Psi^{(b)}).$$

**Variance estimator (eq. 4).** With bootstrap resamples $D^{(1)}, \dots, D^{(M)}$ of the data (the posterior is not refit),

$$\hat V = \operatorname{Var}_{D^{(m)}}\big\{E_{\Psi \mid D}[\Delta(D^{(m)}, \Psi)]\big\} + \operatorname{Var}_{\Psi \mid D}[\Delta(D, \Psi)],$$

a naive bootstrap variance plus a posterior-variance correction for nuisance-parameter uncertainty.

**Contraction assumption.** There are rates $\epsilon_{nt}, \epsilon_{ny} \to 0$ and constants $M_t, M_y$ with $\sup_{P_0}E_{P_0}P_n(n^{-1/2}\|p_t - p_t^*\| > M_t\epsilon_{nt} \mid D) \to 0$ (a) and the analogue for $m_t$ with $\epsilon_{ny}$ (b), where $P_n$ is the posterior and $p_t^*, m_t^*$ are the true values.

**Theorem 1 (double robustness).** Under positivity, unconfoundedness, SUTVA, regularity conditions, and both (a) and (b),

$$\sup_{P_0}E_{P_0}P_n\big(|\Delta(D,\Psi) - \Delta^*| > M\epsilon_n \mid D\big) \to 0, \qquad \epsilon_n = \max(n^{-1/2}, \epsilon_{nt}\epsilon_{ny}) \quad\text{(eq. 5)}.$$

If only one of (a), (b) holds, with rate $\eta_n$, then (eq. 5) holds with $\epsilon_n = \max(n^{-1/2}, \eta_n)$. Hence the posterior mean $\hat\Delta$ is consistent if either nuisance model is right.

**Theorem 2.** Under the conditions of Theorem 1 and further regularity conditions, if (a) and (b) both hold at rates faster than $n^{-1/4}$, then $\hat V - V = o_p(n^{-1})$, where $V$ is the true variance of $\hat\Delta$.

## Expansion

The error of $\Delta(D,\Psi)$ splits into a centred empirical average (order $n^{-1/2}$) plus a bias term that is a product of propensity and outcome-model errors, which gives the $\epsilon_{nt}\epsilon_{ny}$ rate and the double robustness. The correction term in $\hat V$ uses the fact (Freedman, 1999) that the posterior variance of a smooth functional approximates the sampling variance of its posterior mean, which is exactly the parameter uncertainty that resampling with a fixed posterior ignores. The source uses spike-and-slab priors on Gaussian-process or spline basis expansions for the two models in high dimensions.

## Sources

- J. Antonelli, G. Papadogeorgou and F. Dominici, *Causal inference in high dimensions: a marriage between Bayesian modeling and good frequentist properties*, Biometrics 78 (2022), 100-114. <https://doi.org/10.1111/biom.13417> (PMCID: PMC8209114)
