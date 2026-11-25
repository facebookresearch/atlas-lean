# The Itô form of the Ornstein–Uhlenbeck solution as a limit of Riemann sums

Let $B$ be a real Brownian motion, $\theta, \sigma \in \mathbb{R}$, and $X_0$ any real random variable. Then almost surely,
for every $t \ge 0$, the Itô–Riemann sums

$$e^{-\theta t} X_0 + \sigma e^{-\theta t} \sum_{k < n} e^{\theta t k/n} \bigl( B_{t(k+1)/n} - B_{tk/n} \bigr)$$

of $e^{-\theta t} X_0 + \sigma \int_0^t e^{-\theta(t - s)}\, dB_s$ converge as $n \to \infty$ to the [pathwise
solution](../ornstein-uhlenbeck-process/ou-path-solution.md) of the Langevin equation driven by
$u \mapsto B_{\max(u, 0)}$ and started at $X_0$.
