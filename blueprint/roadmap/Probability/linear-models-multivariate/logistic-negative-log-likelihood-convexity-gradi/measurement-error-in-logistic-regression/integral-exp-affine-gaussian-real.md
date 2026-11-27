# Regression calibration is exact for a log-linear risk

For all $\alpha, \beta, m \in \mathbb{R}$ and $\tau^2 \ge 0$,

$$\int e^{\alpha + \beta x}\,d\mathcal N(m, \tau^2)(x) = e^{\alpha + \beta^2\tau^2/2 + \beta m}.$$

If $X \mid W = w \sim \mathcal N(m(w), \tau^2)$, the induced risk is log-linear in the calibrated covariate $m(w)$ with the same slope $\beta$; only the intercept moves.
