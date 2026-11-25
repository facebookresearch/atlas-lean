# Covariance of the stationary damper response

Let `c > 0` and `k`, `σ` be real numbers, and let `X` be a
[stationary Ornstein–Uhlenbeck process](../../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/is-stationary-ornstein-uhlenbeck.md)
indexed by times `t ≥ 0`, with rate `k / c` and noise amplitude `σ / c`, under a measure `P` (a
centred Gaussian process with positive rate, so `P` is a probability measure and `k > 0`). Then for
all times `s, t ≥ 0`,

`cov(X_s, X_t) = σ² / (2 c k) · e^{-(k / c) |t - s|}`.
