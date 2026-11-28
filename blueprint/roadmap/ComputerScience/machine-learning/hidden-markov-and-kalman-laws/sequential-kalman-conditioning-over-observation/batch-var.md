# Batch conditional variance of the final state

Consider the scalar linear-Gaussian model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$ with prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. The batch (joint Gaussian, Schur complement) conditional variance of $x_1$ given $(y_0, y_1)$ is

$$\sigma^2_{x_1 \mid y} = F^2 P_0 + Q - \Sigma_{xy} \cdot \Sigma_{yy}^{-1}\, \Sigma_{xy},$$

with $\Sigma_{xy} = (F H_0 P_0,\ H_1(F^2 P_0 + Q))$ and $\Sigma_{yy}$ the observation covariance matrix (inverse taken as $0$ when singular).
