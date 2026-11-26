# Batch conditional mean of the final state

Consider the scalar linear-Gaussian model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$ with prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. Given an observation vector $y = (y_0, y_1) \in \mathbb{R}^2$, the batch (joint Gaussian, Schur complement) conditional mean of $x_1$ is

$$\mu_{x_1 \mid y} = F m_0 + \Sigma_{xy} \cdot \Sigma_{yy}^{-1}\big(y - (H_0 m_0,\ H_1 F m_0)\big),$$

with $\Sigma_{xy} = (F H_0 P_0,\ H_1(F^2 P_0 + Q))$ and $\Sigma_{yy}$ the observation covariance matrix. The matrix inverse is the inverse when $\Sigma_{yy}$ is invertible and $0$ otherwise.
