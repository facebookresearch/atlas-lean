# Exact bias of the AIPW score integral

Let $\mu$ be a finite measure, $m$ a sub-$\sigma$-algebra, $T$ a measurable treatment event, $Y = Y_1$ on $T$ and $Y_0$ off $T$ $\mu$-a.e., $Y_0, Y_1$ integrable, and assume mean exchangeability: $\mu[\mathbf 1_T Y_1 \mid m] = e^* \mu_1^*$ and $\mu[\mathbf 1_{T^c} Y_0 \mid m] = (1 - e^*)\mu_0^*$ $\mu$-a.e., where $e^* = \mu[\mathbf 1_T \mid m]$ and $\mu_a^* = \mu[Y_a \mid m]$ are conditional expectations. Let $e, g_0, g_1$ be $m$-measurable, $g_0, g_1$ integrable, and $\varepsilon \le e \le 1 - \varepsilon$ $\mu$-a.e. for some $\varepsilon > 0$. For the score $\psi = g_1 + \mathbf 1_T (Y - g_1)/e - g_0 - \mathbf 1_{T^c}(Y - g_0)/(1 - e)$,

$$\int \psi \, d\mu - \int (Y_1 - Y_0) \, d\mu = \int (e^* - e)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right) d\mu.$$

When $\mu$ is a probability measure, the left side is the bias of the score as an estimator of the average treatment effect.
