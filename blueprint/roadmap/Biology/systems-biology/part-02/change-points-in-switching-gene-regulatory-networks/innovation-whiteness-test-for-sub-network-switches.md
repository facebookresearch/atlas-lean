# Innovation whiteness test for sub-network switches

**Setting.** Observations $y_t \in \mathbb{R}^m$ of gene expression changes follow a linear-in-parameters model

$$y_t = H_t\,\theta_{\sigma(t)} + v_t, \qquad v_t \sim \mathcal{N}(0, R)\ \text{i.i.d.},$$

where the regressor matrix $H_t$ is built from measured expression levels, $\theta_1,\dots,\theta_K$ are the parameter vectors (edge weights) of $K$ static sub-networks, and $\sigma(t)\in\{1,\dots,K\}$ is a piecewise-constant switching signal. Run the Kalman filter for a *constant* parameter, started from an unbiased Gaussian prior $\hat\theta_0 \sim \mathcal{N}(\theta, P_0)$ independent of the noise:

$$S_t = H_tP_{t-1}H_t^\top + R,\quad K_t = P_{t-1}H_t^\top S_t^{-1},\quad \hat\theta_t = \hat\theta_{t-1} + K_t e_t,\quad P_t = (I - K_tH_t)P_{t-1},$$

with innovations $e_t = y_t - H_t\hat\theta_{t-1}$ and normalized innovations $\varepsilon_t = S_t^{-1/2}e_t$.

**Theorem.** If $\sigma$ is constant on $[t_0, t_1]$ and the filter is initialized consistently at $t_0$, then $\varepsilon_{t_0},\dots,\varepsilon_{t_1}$ are independent $\mathcal{N}(0, I_m)$ vectors, and

$$Q = \sum_{t=t_0}^{t_1}\|\varepsilon_t\|^2 \sim \chi^2_{m(t_1-t_0+1)} .$$

Under a non-degeneracy assumption ensuring that a switch changes the predicted output ($H_t\theta_k \ne H_t\theta_l$ for some $t$ when $k\ne l$), the converse holds: if a switch occurs in $[t_0,t_1]$, the normalized innovations are no longer i.i.d. standard normal. A switch is declared when $Q$ exceeds the chi-square quantile at the chosen confidence level.

## Expansion

Under a constant parameter the model is a linear Gaussian state-space system with state $\theta$ and trivial dynamics, and the recursion above is its Kalman filter. Standard Kalman theory gives $e_t \mid y_{1:t-1} \sim \mathcal{N}(0, S_t)$, so $\varepsilon_t$ is standard normal and independent of the past innovations (the innovations are a whitened, causal invertible transform of the observations). A sum of squares of independent standard normal coordinates is chi-square with $m$ degrees of freedom per time step. After a switch from $\theta_k$ to $\theta_l$, the innovation acquires the mean $H_t(\theta_l - \hat\theta_{t-1})$ that does not vanish in general, destroying zero mean and independence. Repeating the test on sliding windows locates the change points, after which each segment is identified as a static network.

## Sources

- J. Xiong, T. Zhou, "A Kalman-filter based approach to identification of time-varying gene regulatory networks", PLoS ONE 8(10) (2013) e74571, Theorem 1 and Corollaries 1–2 (Equations 5–10), <https://doi.org/10.1371/journal.pone.0074571>, PMCID PMC3792119.
- R. E. Kalman, "A new approach to linear filtering and prediction problems", Journal of Basic Engineering 82 (1960) 35–45, <https://doi.org/10.1115/1.3662552>.
