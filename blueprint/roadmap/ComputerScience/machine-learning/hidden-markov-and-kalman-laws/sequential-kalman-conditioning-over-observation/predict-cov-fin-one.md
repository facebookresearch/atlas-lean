# Scalar Kalman predict step: variance

A belief over a scalar state is a pair of a mean $m$ and a variance $P$ (a $1 \times 1$ mean vector and covariance matrix). For real $F$ and $Q$, the Kalman predict step with state-transition matrix $(F)$ and process covariance $(Q)$ maps a belief with variance $P$ to a belief with variance

$$P^- = F^2 P + Q .$$
