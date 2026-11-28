# Cross-covariance formula for the final state and the observations

Let $F, H_0, H_1, Q, R_0, R_1, m_0, P_0$ be real numbers, read as the parameters of the scalar linear model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$: prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. The cross-covariance formula for $x_1$ and $(y_0, y_1)$ is the vector

$$\Sigma_{xy} = \big(F H_0 P_0,\ H_1 (F^2 P_0 + Q)\big) \in \mathbb{R}^2 .$$

This is a formula in the parameters. It is the cross-covariance of $x_1$ with $(y_0, y_1)$ when $x_0, w, v_0, v_1$ are independent with variances $P_0, Q, R_0, R_1$.
