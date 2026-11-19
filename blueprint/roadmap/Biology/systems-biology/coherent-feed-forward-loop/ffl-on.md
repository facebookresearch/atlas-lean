# Feed-forward loop target after an ON step

Let $\alpha_y, \beta_y, \alpha_z, \beta_z, K_{xz}, K_{yz} \in \mathbb{R}$. The feed-forward loop target
after an ON step of the input signal at time $0$ (input level $X^* = 1$), starting from
$Y(0) = Z(0) = 0$, is the [relaxation solution](relaxation.md) $z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha(t - s)} P(s)\, ds$ with $\alpha = \alpha_z$, $z_0 = 0$ and production rate $P(s)$
the [AND-gate rate](and-gate.md) with thresholds $K_{xz}, K_{yz}$ and maximal rate $\beta_z$ at the
inputs $1$ and $Y(s)$, where $Y(t) = (\beta_y/\alpha_y)(1 - e^{-\alpha_y t})$ is the [intermediate factor](y-on.md).
