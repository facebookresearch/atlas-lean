# Ornstein–Uhlenbeck process from a deterministic start

Let $B$ be a real Brownian motion, $\theta > 0$, $\sigma \in \mathbb{R}$ and $x_0 \in \mathbb{R}$, and let $X_t$ be the pathwise
solution of the Langevin equation driven by $B$ from $x_0$. Then $X_t = e^{-\theta t} x_0 + Y_t$, where $Y$, the
pathwise solution from $0$, is an Ornstein–Uhlenbeck process started at zero. Hence, for $s, t \ge 0$, $X_t$ is Gaussian
with mean $e^{-\theta t} x_0$ and variance $\sigma^2 (1 - e^{-2\theta t})/(2\theta)$, and
$\operatorname{Cov}(X_s, X_t) = \frac{\sigma^2}{2\theta}\bigl(e^{-\theta\lvert t - s\rvert} - e^{-\theta(s + t)}\bigr)$; the
variance is $0$ at $t = 0$ and tends to $\sigma^2/(2\theta)$.

The decomposition holds because the pathwise solution is affine in the starting value with coefficient
$e^{-\theta t}$; the law of $Y$ is that of the Ornstein–Uhlenbeck process started at zero.

## Depends on

- [Pathwise solution of the Langevin equation](ou-path-solution.md)
- [Ornstein–Uhlenbeck process started at zero](is-ornstein-uhlenbeck-from-zero.md)

## Proof depends on

- [The pathwise Langevin solution is an Ornstein–Uhlenbeck process](is-ornstein-uhlenbeck-from-zero-ou-path.md), for $Y$
- [One-time law of the Ornstein–Uhlenbeck process from zero](has-law-eval.md), for the variance
- [Covariance of the Ornstein–Uhlenbeck process started at zero](ou-covariance.md), for the covariance

## Sources

- M. Holmes-Cerfon, *Applied Stochastic Analysis*, lecture notes, spring 2022, Lecture 8 (Stochastic differential equations), Example 8.3, Equation (4) and the computation of the mean and covariance, <https://personal.math.ubc.ca/~holmescerfon/teaching/asa22/handout-Lecture8_2022.pdf>.
