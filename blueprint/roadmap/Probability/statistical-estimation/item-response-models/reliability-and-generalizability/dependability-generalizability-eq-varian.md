# Dependability and generalizability as variance ratios

In a crossed person-by-item design with $m \ge 1$ items (on a probability space), write $X_{pi} = \mu + P_p + I_i + e_{pi}$, the absolute error $\Delta_p = \frac1m\sum_iX_{pi} - (\mu + P_p)$ and the relative error $\delta_p = \frac1m\sum_iX_{pi} - (\mu + P_p + \frac1m\sum_iI_i)$. Fix a person $p$ with $\operatorname{Var}(P_p) = \sigma_P^2$, square-integrable item effects and residuals with $\operatorname{Cov}(I_i, I_j) = \sigma_I^2\mathbf 1[i = j]$, $\operatorname{Cov}(e_{pi}, e_{pj}) = \sigma_e^2\mathbf 1[i = j]$ and $\operatorname{Cov}(I_i, e_{pj}) = 0$. Then

$$\Phi = \frac{\operatorname{Var}(P_p)}{\operatorname{Var}(P_p) + \operatorname{Var}(\Delta_p)}, \qquad E\rho^2 = \frac{\operatorname{Var}(P_p)}{\operatorname{Var}(P_p) + \operatorname{Var}(\delta_p)},$$

where $\Phi = \sigma_P^2/(\sigma_P^2 + (\sigma_I^2 + \sigma_e^2)/m)$ and $E\rho^2 = \sigma_P^2/(\sigma_P^2 + \sigma_e^2/m)$ (both $0$ at a zero denominator).
