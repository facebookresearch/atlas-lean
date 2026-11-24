# Explicit Gaussian random-intercept model

For real $\sigma_b^2$ and $\sigma_e^2$, the explicit model gives the cell $(d, c)$ the value

$$Y_{(d, c)}(\omega) = \sqrt{\sigma_b^2}\, Z_d(\omega) + \sqrt{\sigma_e^2}\, W_{(d, c)}(\omega)$$

at a point $\omega$ of the [noise space](noise-space.md), with coordinates $Z_d$ and $W_{(d, c)}$.
With the convention $\sqrt x = 0$ for $x < 0$, a negative variance component contributes nothing.
Under the [independent standard Gaussian coordinates](std-gaussian-pi.md) and for
$\sigma_b^2, \sigma_e^2 \ge 0$ it is a [random-intercept model](is-random-intercept-ri-model.md).
