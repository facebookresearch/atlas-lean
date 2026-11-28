# Scalar Kalman gain

A belief over a scalar state is a pair of a mean $m$ and a variance $P$ (a $1 \times 1$ mean vector and covariance matrix). For real $H$ and $R$, the Kalman gain with observation matrix $(H)$ and observation-noise covariance $(R)$ at a belief with variance $P$ is

$$K = \frac{P\, H}{H^2 P + R},$$

with the convention $t/0 = 0$ (the $1 \times 1$ matrix inverse of $0$ is $0$).
