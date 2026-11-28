# Predicted beliefs of the Kalman filter

For $j \in \mathbb{N}$ let $F_j$ be real
$n \times n$ matrices, $G_j$ real $n \times r$ matrices, $Q_j$ real $r \times r$ matrices, $H_j$
real $n \times p$ matrices and $R_j$ real $p \times p$ matrices, and let $b_0$ be a belief with mean
$\bar x_0$ and covariance $P_0$. For observations $z_0, \dots, z_{k-1} \in \mathbb{R}^p$, the
predicted belief $(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is defined by recursion on $k$. It is
$(\bar x_0, P_0)$ for $k = 0$, and

$$\hat x_{k+1|k} = F_k \hat x_{k|k}, \qquad
\Sigma_{k+1|k} = F_k \Sigma_{k|k} F_k^\top + G_k Q_k G_k^\top,$$

where $(\hat x_{k|k}, \Sigma_{k|k})$ is the update of $(\hat x_{k|k-1}, \Sigma_{k|k-1})$ with
observation matrix $H_k^\top$, noise covariance $R_k$ and observation $z_k$:
$\hat x_{k|k} = \hat x_{k|k-1} + K_k (z_k - H_k^\top \hat x_{k|k-1})$ and
$\Sigma_{k|k} = (I - K_k H_k^\top) \Sigma_{k|k-1}$ with the gain
$K_k = \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1}$, where the inverse is taken to
be $0$ when the matrix is singular.

In the linear Gaussian signal model with horizon $N \ge k$, $x_{j+1} = F_j x_j + G_j w_j$ for
$j < N$ and $z_j = H_j^\top x_j + v_j$ for $j \le N$, with mutually independent
$x_0 \sim N(\bar x_0, P_0)$, $w_j \sim N(0, Q_j)$ and $v_j \sim N(0, R_j)$, $P_0$ and $Q_j$
positive semidefinite and $R_j$ positive definite, $N(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is the
conditional law of $x_k$ given $z_0, \dots, z_{k-1}$ for almost every history under its law
(`condDistrib_observationHistory`). When one of the inverted matrices is singular, the zero
inverse is only a convention, and the predicted belief need not be that conditional law.
