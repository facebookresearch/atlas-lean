# Covariance-matrix formula for the observation pair

Let $F, H_0, H_1, Q, R_0, R_1, m_0, P_0$ be real numbers, read as the parameters of the scalar linear model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$: prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. The covariance-matrix formula for the observation pair $(y_0, y_1)$ is

$$\Sigma_{yy} = \begin{pmatrix} H_0^2 P_0 + R_0 & H_0 H_1 F P_0 \\ H_0 H_1 F P_0 & H_1^2 (F^2 P_0 + Q) + R_1 \end{pmatrix}.$$

This is a formula in the parameters. It is the covariance matrix of $(y_0, y_1)$ when $x_0, w, v_0, v_1$ are independent with variances $P_0, Q, R_0, R_1$.
