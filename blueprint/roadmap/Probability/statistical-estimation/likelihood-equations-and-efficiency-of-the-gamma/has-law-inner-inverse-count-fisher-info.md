# Gaussian law of the projections of the MLE limit

Let $a, b, \sigma > 0$ and $\tau > \sigma / (a (b + \sigma))$, so that the
[Fisher information matrix](count-fisher-info.md) $I = I(a, b, \sigma, \tau)$ is invertible. Let $Y$
be a random vector in $\mathbb{R}^2$ on a measure space $(\Omega', P')$ with
$\langle Y, t \rangle \sim N(0, \langle I t, t \rangle)$ under $P'$ for every $t \in \mathbb{R}^2$
(which forces $P'$ to be a probability measure). Then for every $u \in \mathbb{R}^2$,
$\langle I^{-1} Y, u \rangle \sim N(0, \langle I^{-1} u, u \rangle)$.
