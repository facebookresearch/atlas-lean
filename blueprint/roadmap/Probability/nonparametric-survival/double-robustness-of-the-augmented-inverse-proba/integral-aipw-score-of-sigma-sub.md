# Exact bias of the AIPW score

Let $m$ be a sub-$\sigma$-algebra, $T$ a measurable treatment event, $Y = Y_1$ on $T$ and $Y_0$ off $T$ almost surely, $Y_0, Y_1$ integrable, and assume mean exchangeability: $E[\mathbf 1_T Y_1 \mid m] = e^* \mu_1^*$ and $E[\mathbf 1_{T^c} Y_0 \mid m] = (1 - e^*)\mu_0^*$, where $e^* = P(T \mid m)$, $\mu_a^* = E[Y_a \mid m]$. Let $e, g_0, g_1$ be $m$-measurable, $g_0, g_1$ integrable, and $\varepsilon \le e \le 1 - \varepsilon$ almost surely for some $\varepsilon > 0$. For the score $\psi = g_1 + \mathbf 1_T (Y - g_1)/e - g_0 - \mathbf 1_{T^c}(Y - g_0)/(1 - e)$,

$$E[\psi] - E[Y_1 - Y_0] = E\left[(e^* - e)\left(\frac{\mu_1^* - g_1}{e} + \frac{\mu_0^* - g_0}{1 - e}\right)\right].$$
