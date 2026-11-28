# Rare-event regression calibration for the logistic model

Write $\sigma(t) = 1/(1 + e^{-t})$ for the logistic function. For all $\alpha, \beta, m$ and $\tau^2 \ge 0$, with $R = e^{\alpha + \beta^2\tau^2/2 + \beta m}$,

$$R - \int\sigma(\alpha + \beta x)\,d\mathcal N(m, \tau^2)(x) \le e^{2\alpha + 2\beta^2\tau^2 + 2\beta m} = R^2e^{\beta^2\tau^2}.$$
