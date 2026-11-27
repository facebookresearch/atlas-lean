# Filtered beliefs of the Kalman filter

For $j \in \mathbb{N}$ let $F_j$ be real
$n \times n$ matrices, $G_j$ real $n \times r$ matrices, $Q_j$ real $r \times r$ matrices, $H_j$
real $n \times p$ matrices and $R_j$ real $p \times p$ matrices, and let $b_0$ be a belief with mean
$\bar x_0$ and covariance $P_0$. For observations $z_0, \dots, z_k \in \mathbb{R}^p$, the filtered
belief $(\hat x_{k|k}, \Sigma_{k|k})$ is

$$\hat x_{k|k} = \hat x_{k|k-1} + K_k (z_k - H_k^\top \hat x_{k|k-1}), \qquad
\Sigma_{k|k} = (I - K_k H_k^\top) \Sigma_{k|k-1},$$

with the gain $K_k = \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1}$, where
$(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is the predicted belief of the Kalman filter with these matrices
and $b_0$ after $z_0, \dots, z_{k-1}$, and the inverse is taken to be $0$ when the matrix is
singular.
