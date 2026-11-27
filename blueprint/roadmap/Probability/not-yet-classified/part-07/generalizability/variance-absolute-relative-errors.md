# Variances of absolute and relative errors

Let $\mu$ be a probability measure, and let finite nonempty sets of persons $p$ and $m$ items $i$ have scores $X_{pi} = \mu_0 + P_p + I_i + e_{pi}$ with a constant $\mu_0$ and square-integrable effects of mean zero. Assume $\operatorname{Cov}(P_p, P_q) = \sigma_P^2 [p = q]$, $\operatorname{Cov}(I_i, I_j) = \sigma_I^2 [i = j]$, $\operatorname{Cov}(e_{pi}, e_{qj}) = \sigma_e^2 [(p, i) = (q, j)]$, all covariances between different effect families are zero, and $\sigma_P^2, \sigma_I^2, \sigma_e^2 \ge 0$. For a person $p$ let $\bar X_p$ and $\bar I$ be the means of $X_{pi}$ and $I_i$ over the $m$ items, $\Delta_p = \bar X_p - (\mu_0 + P_p)$ the absolute error and $\delta_p = \bar X_p - (\mu_0 + P_p + \bar I)$ the relative error. Then

$$\operatorname{Var}(\Delta_p) = \frac{\sigma_I^2 + \sigma_e^2}{m}, \qquad \operatorname{Var}(\delta_p) = \frac{\sigma_e^2}{m}.$$
