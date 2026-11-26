# Recursive Kalman filtering equals batch conditioning for two observations

Consider the scalar linear-Gaussian model $x_1 = F x_0 + w$, $y_0 = H_0 x_0 + v_0$, $y_1 = H_1 x_1 + v_1$ with prior mean $m_0$ and variance $P_0$ of $x_0$, process variance $Q$ and observation variances $R_0, R_1$. Let $F, Q, H_0, H_1, R_0, R_1$ be real with $Q \ge 0$, $R_0 > 0$ and $R_1 > 0$, and let the initial belief have mean $m_0$ and variance $P_0 \ge 0$. Run the scalar Kalman filter: update with $y_0$ (observation matrix $H_0$, noise $R_0$), then one step consisting of a predict (transition $F$, process noise $Q$) and an update with $y_1$ (observation matrix $H_1$, noise $R_1$). The resulting belief has mean and variance

$$\mu_{x_1 \mid y} = F m_0 + \Sigma_{xy} \cdot \Sigma_{yy}^{-1}\big(y - (H_0 m_0, H_1 F m_0)\big), \qquad \sigma^2_{x_1\mid y} = F^2 P_0 + Q - \Sigma_{xy} \cdot \Sigma_{yy}^{-1} \Sigma_{xy},$$

the one-shot joint Gaussian conditioning of $x_1$ on $y = (y_0, y_1)$, where

$$\Sigma_{yy} = \begin{pmatrix} H_0^2 P_0 + R_0 & H_0 H_1 F P_0 \\ H_0 H_1 F P_0 & H_1^2 (F^2 P_0 + Q) + R_1 \end{pmatrix}, \qquad \Sigma_{xy} = \big(F H_0 P_0,\ H_1(F^2 P_0 + Q)\big).$$

This is an identity of parameter formulas; it makes no statement about random variables or conditional laws.
