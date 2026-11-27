# Stationary Ornstein–Uhlenbeck process

Let $\theta, \sigma \in \mathbb{R}$ and let $P$ be a measure. A real process $X = (X_t)_{t \ge 0}$ is a stationary
Ornstein–Uhlenbeck process with rate $\theta$ and noise amplitude $\sigma$ under $P$ if

1. $\theta > 0$;
2. $X$ is a Gaussian process under $P$;
3. $\mathbb E X_t = 0$ for every $t$;
4. $\operatorname{Cov}(X_s, X_t) = \frac{\sigma^2}{2\theta} e^{-\theta|t - s|}$ for all $s, t$, the [stationary
   covariance](ou-stationary-covariance.md).

Only the finite-dimensional laws are fixed.
