# Observed cell values

For real $\mu_0$, $\tau$, $\beta$ and a noise process $U_i : \Omega \to \mathbb{R}$, one for each
cell $i = (d, c)$, the observed value of cell $i = (d, c)$ at $\omega \in \Omega$ is the
[donor mean](mean-fn.md) $m(d) = \mu_0 + \tau\, \mathrm{cond}(d) + \beta\, \mathrm{batch}(d)$ plus
the noise:

$$Y_i(\omega) = m(d) + U_i(\omega).$$

The noise is arbitrary, for example a [random-intercept model](is-random-intercept.md).
