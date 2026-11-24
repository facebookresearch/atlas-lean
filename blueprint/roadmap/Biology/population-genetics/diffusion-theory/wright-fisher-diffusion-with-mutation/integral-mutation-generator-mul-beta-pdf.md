# Weak stationarity of Wright's law, density form

For all real $\theta_1 > 0$ and $\theta_2 > 0$ and every function $f$ twice continuously differentiable on $[0, 1]$,

$$\int_0^1 (L_{\theta_1,\theta_2} f)(x)\, \beta_{\theta_1,\theta_2}(x)\, dx = 0,$$

where $L_{\theta_1,\theta_2}$ is the [mutation generator](mutation-generator.md) and $\beta_{\theta_1,\theta_2}$ the Beta density. The proof integrates by parts: since the flux vanishes, $(L f)\,\beta$ is the derivative of $x^{\theta_1}(1 - x)^{\theta_2} f'(x)/(2B(\theta_1, \theta_2))$ on $(0, 1)$, which vanishes at both endpoints because $\theta_1, \theta_2 > 0$.
