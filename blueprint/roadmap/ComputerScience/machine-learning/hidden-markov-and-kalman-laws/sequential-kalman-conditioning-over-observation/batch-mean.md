# Batch conditioning formula for the mean of the final state

Let $F, H_0, H_1, Q, R_0, R_1, m_0, P_0$ be real numbers, read as the parameters of the scalar linear model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$: prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. For an observation vector $y = (y_0, y_1) \in \mathbb{R}^2$, the batch conditioning formula for the mean of $x_1$ is the Schur-complement expression

$$\mu_{x_1 \mid y} = F m_0 + \Sigma_{xy} \cdot \Sigma_{yy}^{-1}\big(y - (H_0 m_0,\ H_1 F m_0)\big),$$

where $\Sigma_{xy} = (F H_0 P_0,\ H_1(F^2 P_0 + Q))$ is the [cross-covariance formula](batch-cov-xy.md) and $\Sigma_{yy}$ the [covariance-matrix formula](batch-cov-y.md) of the observation pair.

This is a formula in the parameters, with $\Sigma_{yy}^{-1}$ taken as $0$ when $\Sigma_{yy}$ is singular; it makes no statement about random variables. It is the conditional mean of $x_1$ given $(y_0, y_1)$ when $x_0, w, v_0, v_1$ are independent and jointly Gaussian, the noises $w, v_0, v_1$ are centred, and $\Sigma_{yy}$ is invertible; the law-level result is `KalmanFilter.condDistrib_observationHistory`. When $\Sigma_{yy}$ is singular the formula reduces to $F m_0$, which need not be the conditional mean.
