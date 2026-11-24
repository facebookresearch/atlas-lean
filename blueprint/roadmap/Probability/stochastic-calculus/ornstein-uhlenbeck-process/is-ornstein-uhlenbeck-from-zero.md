# Ornstein–Uhlenbeck process started at zero

Let $\theta, \sigma \in \mathbb{R}$ and let $P$ be a measure. A real process $X = (X_t)_{t \ge 0}$ is an Ornstein–Uhlenbeck
process started at zero with rate $\theta$ and noise amplitude $\sigma$ under $P$ if

1. $\theta > 0$;
2. $X$ is a Gaussian process under $P$;
3. $\mathbb E X_t = 0$ for every $t$;
4. $\operatorname{Cov}(X_s, X_t) = c(s, t)$ for all $s, t$, where $c$ is the [Ornstein–Uhlenbeck
   covariance](ou-covariance.md) $\frac{\sigma^2}{2\theta}\bigl(e^{-\theta|t - s|} - e^{-\theta(t + s)}\bigr)$.

Only the finite-dimensional laws are fixed; no path regularity is required.
