# Variation-of-constants solution of a linear relaxation equation

For real $\alpha$, $z_0$ and $t$ and a production rate $P \colon \mathbb{R} \to \mathbb{R}$, the
variation-of-constants solution of $z' = P(t) - \alpha z$, $z(0) = z_0$, is

$$z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha (t - s)} P(s)\, ds,$$

where the oriented integral is taken to be $0$ when the integrand is not integrable between $0$ and
$t$. It is used for $t \ge 0$.
