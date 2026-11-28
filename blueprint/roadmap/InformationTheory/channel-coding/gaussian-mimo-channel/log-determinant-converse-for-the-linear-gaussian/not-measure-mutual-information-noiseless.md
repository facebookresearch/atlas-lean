# The log-determinant converse needs positive definite noise

Positive definite noise cannot be dropped from the log-determinant converse. Take one dimension, $H = 1$, input law $\mathcal{N}(0, 1)$ on $\mathbb{R}^1$ and noise covariance $R = 0$, so that the noise kernel sends $x$ to $\delta_x$ and $Y = X$. Then the mutual information of the joint law is not bounded by the log-determinant expression

$$\max\left\{\frac{1}{2\ln 2}\ln\frac{\det(0 + 1 \cdot 1 \cdot 1^\top)}{\det 0},\ 0\right\},$$

which equals $0$ under the conventions $1/0 = 0$ and $\ln 0 = 0$, so the mutual information is positive.
