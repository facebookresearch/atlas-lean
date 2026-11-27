# Sequential exchangeability and the g-formula

Fix $K \ge 1$ time points, finite-valued covariates $L_0, \dots, L_{K-1}$, treatments
$A_0, \dots, A_{K-1}$ and an outcome $Y$, observed in the order $L_0, A_0, L_1, A_1, \dots, Y$, and a static
treatment regime $\bar a = (a_0, \dots, a_{K-1})$ with counterfactual outcome $Y^{\bar a}$ and
counterfactual covariates $L_t^{\bar a}$. Write $\bar l_t = (l_0, \dots, l_t)$ and
$\bar a_t = (a_0, \dots, a_t)$. Assume consistency (if $\bar A = \bar a$ then $Y = Y^{\bar a}$, and
likewise for covariates), sequential exchangeability ($Y^{\bar a}$ is independent of $A_t$ given
$\bar L_t = \bar l_t$ and $\bar A_{t-1} = \bar a_{t-1}$, for every $t$) and positivity
($P(A_t = a_t \mid \bar L_t = \bar l_t, \bar A_{t-1} = \bar a_{t-1}) > 0$ whenever the conditioning event has
positive probability). Then

$$\mathbb{E}[Y^{\bar a}] = \sum_{\bar l} \mathbb{E}[Y \mid \bar L = \bar l, \bar A = \bar a] \prod_{t=0}^{K-1} P(L_t = l_t \mid \bar L_{t-1} = \bar l_{t-1}, \bar A_{t-1} = \bar a_{t-1}),$$

the sum ranging over covariate histories whose conditioning events have positive probability.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: longitudinal potential outcomes under static treatment regimes, with consistency, sequential exchangeability and positivity.

## Related topics

- [The intervention $\mathrm{do}(X_k = a)$](causal-bayesian-networks/intervene.md)

## Sources

- M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC (author copy, January 2025 revision): sequential exchangeability (Section 19.4) and the g-formula for time-varying treatments (Section 21.1). <https://static1.squarespace.com/static/675db8b0dd37046447128f5f/t/677676888e31cc50c2c33877/1735816881944/hernanrobins_WhatIf_2jan25.pdf>
