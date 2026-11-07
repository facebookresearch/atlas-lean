# Schur form of the updated covariance

Let $H$ be a real $p \times n$ matrix, $R$ a real
$p \times p$ matrix and $y \in \mathbb{R}^p$, and let a belief have covariance $P$. Then the
covariance of the belief updated with $H$, $R$ and $y$ equals
$P - P H^\top (H P H^\top + R)^{-1} H P$. Here $M^{-1}$ is the matrix inverse, taken to be $0$
when $M$ is singular, so no invertibility is assumed.

With the Kalman gain $K = P H^\top (H P H^\top + R)^{-1}$ this says $(I - K H) P =
P - P H^\top (H P H^\top + R)^{-1} H P$.
