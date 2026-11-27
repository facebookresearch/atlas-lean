# Relaxation solution satisfies its differential equation

Let $\alpha, z_0, t \in \mathbb{R}$ and let $P \colon \mathbb{R} \to \mathbb{R}$ be integrable on every
bounded interval and continuous at $t$. Then the [relaxation solution](relaxation.md) $z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha(t - s)} P(s)\, ds$ has derivative $P(t) - \alpha z(t)$ at
$t$.
