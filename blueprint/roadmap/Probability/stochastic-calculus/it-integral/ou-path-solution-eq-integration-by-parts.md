# Ornstein–Uhlenbeck path solution by integration by parts

For every path $w : \mathbb{R} \to \mathbb{R}$ and all real $\theta, \sigma, x_0, t$, with $g(u) = e^{\theta u}$, the [pathwise
solution](../ornstein-uhlenbeck-process/ou-path-solution.md) satisfies

$$x(t) = e^{-\theta t} x_0 + \sigma e^{-\theta t} \Bigl( g(t) w(t) - g(0) w(0) - \int_0^t g'(u) w(u)\, du \Bigr) .$$
