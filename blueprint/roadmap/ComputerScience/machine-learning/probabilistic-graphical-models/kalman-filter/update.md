# Kalman filter update

Given a real $p \times n$ observation matrix $H$, a real $p \times p$
matrix $R$, an observation $y \in \mathbb{R}^p$ and a belief with mean $m$ and covariance $P$,
the updated belief has mean $m + K (y - H m)$ and covariance $(I - K H) P$, where
$K = P H^\top (H P H^\top + R)^{-1}$ is the Kalman gain and the matrix inverse is taken to be
$0$ when $H P H^\top + R$ is singular.

It corresponds to observing a state $x$ as $y = H x + v$ with Gaussian noise $v \sim N(0, R)$.
