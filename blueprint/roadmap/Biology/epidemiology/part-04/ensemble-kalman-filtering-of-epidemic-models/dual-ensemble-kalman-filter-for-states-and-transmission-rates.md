# Dual ensemble Kalman filter for states and transmission rates

**State-space model.** Discretize a compartmental epidemic model (e.g. by a Runge–Kutta step) and treat unknown transmission rates $\beta_t$ as a random walk:

$$x_{t+1} = f(x_t, \beta_t) + w_t, \qquad \beta_{t+1} = \beta_t + \eta_t, \qquad y_t = h(x_t, \beta_t) + v_t,$$

where $x_t$ are compartment sizes (e.g. $S, I, R$ and environmental virus $V$), $y_t$ are observed flows (new reported cases $\lambda(I,V)S$, new recoveries $\rho I$, new deaths $dI$), and $w_t$, $\eta_t$, $v_t$ are zero-mean Gaussian noises with covariances $Q_t$, $T_t$, $R_t$.

**Algorithm (perturbed-observation EnKF, one cycle).** Given an analysis ensemble $\{x^{a,i}_t\}_{i=1}^n$ and parameter estimate $\beta^a_t$:

1. *Forecast:* $x^{f,i}_{t+1} = f(x^{a,i}_t, \beta^a_t) + w^i_t$ and $y^{f,i}_{t+1} = h(x^{f,i}_{t+1}, \beta^a_t)$, with ensemble means $\bar x^f_{t+1}$, $\bar y^f_{t+1}$.

2. *Sample covariances:* with anomalies $E^{i}_x = x^{f,i}_{t+1} - \bar x^f_{t+1}$ and $E^{i}_y = y^{f,i}_{t+1} - \bar y^f_{t+1}$,

    $$P_{xy} = \frac{1}{n-1}\sum_{i} E^i_x (E^i_y)^\top, \qquad P_{yy} = \frac{1}{n-1}\sum_{i} E^i_y (E^i_y)^\top .$$

3. *Analysis:* $K_{t+1} = P_{xy}(P_{yy} + R_{t+1})^{-1}$ and $x^{a,i}_{t+1} = x^{f,i}_{t+1} + K_{t+1}\big(y_{t+1} + v^i_{t+1} - y^{f,i}_{t+1}\big)$ with perturbations $v^i_{t+1} \sim \mathcal{N}(0, R_{t+1})$; the state estimate is the mean $x^a_{t+1} = \frac1n\sum_i x^{a,i}_{t+1}$.

4. *Parameter update:* propagate $\beta^{f,i}_{t+1} = \beta^{f,i}_t + \eta^i_t$, predict $y^{\beta,i}_{t+1} = h(x^a_{t+1}, \beta^{f,i}_{t+1})$, form $P_{\beta y}$ and $P_{\beta yy}$ from parameter and output anomalies, and update with the gain $K_{\beta} = P_{\beta y}(P_{\beta yy} + R_{t+1})^{-1}$ in the same way.

**Property.** If $f$ and $h$ are linear and all noises Gaussian, then as $n \to \infty$ the analysis ensemble mean and sample covariance converge to the Kalman filter mean and covariance; for nonlinear epidemic dynamics the EnKF propagates the ensemble through the full nonlinear model and applies a linear (Gaussian) correction, without Jacobians.

## Depends on

- [Kalman filter step](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/step.md)

## Expansion

The Kalman gain $K = P_{xy}(P_{yy} + R)^{-1}$ is the regression coefficient of the state on the predicted observation under a joint Gaussian approximation; perturbing the observations with independent noise of covariance $R$ makes the analysis ensemble spread match the posterior covariance, $(I - KH)P^f$ in the linear case, rather than underestimating it. Alternating a state update at fixed parameters with a parameter update at the filtered state (dual estimation) keeps the augmented problem low-dimensional and stable. Unobserved compartments, such as unreported infections or environmental virus, are reconstructed through their cross-covariance with the observed flows, and the filtered $\beta_t$ yields a time-varying reproduction number and initial conditions for short-term forecasts.

## Sources

- C. Hameni Nkwayep, S. Bowong, J. J. Tewa and J. Kurths, "Short-term forecasts of the COVID-19 pandemic: a study case of Cameroon", Chaos, Solitons & Fractals 140 (2020), 110106, Section 2.2 (Eqs. (4)–(7)) and Appendix C (Eqs. (32)–(45)), <https://doi.org/10.1016/j.chaos.2020.110106>, PMCID: PMC7836758.
- G. Evensen, "The ensemble Kalman filter: theoretical formulation and practical implementation", Ocean Dynamics 53 (2003), 343–367.
