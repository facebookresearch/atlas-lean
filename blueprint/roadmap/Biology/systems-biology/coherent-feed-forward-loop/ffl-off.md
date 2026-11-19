# Feed-forward loop target after an OFF step

Let $\alpha_z, \beta_z, K_{xz}, K_{yz}, z_0 \in \mathbb{R}$ and let $Y \colon \mathbb{R} \to \mathbb{R}$ be
any trajectory of the intermediate factor. The feed-forward loop target after the input signal is
removed at time $0$ (input level $X^* = 0$), starting from $Z(0) = z_0$, is the [relaxation solution](relaxation.md) $z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha(t - s)} P(s)\, ds$ with
$\alpha = \alpha_z$ and production rate $P(s)$ the [AND-gate rate](and-gate.md) with thresholds
$K_{xz}, K_{yz}$ and maximal rate $\beta_z$ at the inputs $0$ and $Y(s)$.
