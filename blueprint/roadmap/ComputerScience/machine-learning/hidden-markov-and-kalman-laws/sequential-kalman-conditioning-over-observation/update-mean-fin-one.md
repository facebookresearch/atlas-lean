# Scalar Kalman update step: mean

A belief over a scalar state is a pair of a mean $m$ and a variance $P$ (a $1 \times 1$ mean vector and covariance matrix). For real $H$, $R$ and an observation $y \in \mathbb{R}$, the Kalman update step with observation matrix $(H)$ and observation-noise covariance $(R)$ maps a belief with mean $m$ and variance $P$ to a belief with mean

$$m^+ = m + K\,(y - H m), \qquad K = \frac{P\, H}{H^2 P + R},$$

with the convention $t/0 = 0$.
