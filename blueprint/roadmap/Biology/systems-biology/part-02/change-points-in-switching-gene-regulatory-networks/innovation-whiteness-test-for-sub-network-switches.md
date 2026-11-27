# Innovation whiteness test for sub-network switches

**Setting.** Observations $y_t \in \mathbb{R}^m$ of gene expression changes follow a linear-in-parameters model

$$y_t = H_t\,\theta_{\sigma(t)} + v_t, \qquad v_t \sim \mathcal{N}(0, R)\ \text{i.i.d.},\quad R \succ 0,$$

where the regressor matrix $H_t$ is a function of the earlier observations $y_1, \dots, y_{t-1}$ (in the source $H_t = I_n \otimes y_{t-1}^\top$) or deterministic, $\theta_1,\dots,\theta_K$ are the parameter vectors (edge weights) of $K$ static sub-networks, and $\sigma(t)\in\{1,\dots,K\}$ is a piecewise-constant switching signal. Run the Kalman filter for a *constant* parameter $\theta$ from a Gaussian prior $(\hat\theta_0, P_0)$, in Bayesian form: $\theta$ is random with law $\mathcal{N}(\hat\theta_0, P_0)$ and independent of $v_1, v_2, \dots$ (for deterministic $H_t$ it is equivalent to take $\theta$ fixed and $\hat\theta_0 \sim \mathcal{N}(\theta, P_0)$ independent of the noise; for $H_t$ depending on past observations that frequentist form does not give white innovations):

$$S_t = H_tP_{t-1}H_t^\top + R,\quad K_t = P_{t-1}H_t^\top S_t^{-1},\quad \hat\theta_t = \hat\theta_{t-1} + K_t e_t,\quad P_t = (I - K_tH_t)P_{t-1},$$

with innovations $e_t = y_t - H_t\hat\theta_{t-1}$ and normalized innovations $\varepsilon_t = S_t^{-1/2}e_t$.

**Theorem.** Suppose $\sigma$ is constant on $[t_0, t_1]$ and the filter is initialized consistently at $t_0$, i.e. restarted at $t_0$ from $(\hat\theta_{t_0-1}, P_{t_0-1})$ where $\theta_{\sigma(t_0)}$ is random and, given $y_1, \dots, y_{t_0-1}$, has law $\mathcal{N}(\hat\theta_{t_0-1}, P_{t_0-1})$ and is independent of $v_{t_0}, v_{t_0+1}, \dots$ (for deterministic $H_t$, an unbiased Gaussian estimate of a fixed $\theta_{\sigma(t_0)}$ independent of the noise suffices). Then $\varepsilon_{t_0},\dots,\varepsilon_{t_1}$ are independent $\mathcal{N}(0, I_m)$ vectors, and

$$Q = \sum_{t=t_0}^{t_1}\|\varepsilon_t\|^2 \sim \chi^2_{m(t_1-t_0+1)} .$$

Under the non-degeneracy assumption that a switch changes the predicted output inside the window, $H_t(\theta_{\sigma(t)} - \theta_{\sigma(t_0)}) \ne 0$ for some $t \in [t_0, t_1]$ after the switch (with positive probability when $H_t$ is random), the converse holds: if a switch occurs in $[t_0,t_1]$, the normalized innovations are no longer i.i.d. standard normal. A switch is declared when $Q$ exceeds the chi-square quantile at the chosen confidence level.

## Depends on

- [Kalman gain](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/gain.md)
- [Kalman filter update](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/update.md)

## Proof depends on

- [The Kalman filter gives the conditional law given the whole observation history](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/kalman-filter-is-the-full-history-posterior.md)

## Expansion

Under a constant parameter the model is a linear Gaussian state-space system with state $\theta$ and trivial dynamics, and the recursion above is its Kalman filter. Standard Kalman theory, in its conditional form for a regressor determined by the past observations, gives $e_t \mid y_{1:t-1} \sim \mathcal{N}(0, S_t)$, so $\varepsilon_t$ is standard normal and independent of the past innovations (the innovations are a whitened, causal invertible transform of the observations). A sum of squares of independent standard normal coordinates is chi-square with $m$ degrees of freedom per time step. After a switch from $\theta_k$ to $\theta_l$, the innovation acquires the mean $H_t(\theta_l - \hat\theta_{t-1})$ that does not vanish in general, destroying zero mean and independence. Repeating the test on sliding windows locates the change points, after which each segment is identified as a static network.

## Sources

- J. Xiong, T. Zhou, "A Kalman-filter based approach to identification of time-varying gene regulatory networks", PLoS ONE 8(10) (2013) e74571, Theorem 1 and Corollaries 1–2 (Equations 5–10), <https://doi.org/10.1371/journal.pone.0074571>, PMCID PMC3792119.
- R. E. Kalman, "A new approach to linear filtering and prediction problems", Journal of Basic Engineering 82 (1960) 35–45, <https://doi.org/10.1115/1.3662552>.
