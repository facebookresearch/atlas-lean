# Slope attenuation for logistic errors in variables

Write $\sigma(t) = 1/(1 + e^{-t})$ for the logistic function. Let $Y$ be a measurable binary label on a probability space with $p = P(Y = 1) \in (0, 1)$. Conditionally on $Y = y$, let the measurable true regressor $X \sim \mathcal N(\mu_y, v)$ with $v > 0$ and the measurable measurement error $U \sim \mathcal N(0, v_u)$ be independent, and observe $W = X + U$. Write $\beta = (\mu_1 - \mu_0)/v$, $\rho = v/(v + v_u)$ and $\alpha(v) = \log\frac{p}{1-p} - \frac{\mu_1 - \mu_0}{v}\cdot\frac{\mu_0 + \mu_1}{2}$. Then for every measurable $A$

- $\int_{\{X \in A\}}\sigma(\alpha(v) + \beta X)\,dP = P(Y = 1,\ X \in A)$: the model in $X$ is exactly logistic with slope $\beta$;
- $\int_{\{W \in A\}}\sigma(\alpha(v + v_u) + \rho\beta W)\,dP = P(Y = 1,\ W \in A)$: the model in $W$ is exactly logistic with the attenuated slope $\rho\beta$;
- dividing the naive slope $\rho\beta$ by $\rho$ recovers $\beta$.
