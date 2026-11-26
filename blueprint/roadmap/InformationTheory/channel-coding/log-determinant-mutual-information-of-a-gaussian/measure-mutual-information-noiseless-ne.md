# Measure Mutual Information noiseless ne log Det

Positive definiteness of the noise covariance cannot be dropped from the log-determinant formula. For the noiseless scalar channel $Y = X$ with $X \sim \mathcal{N}(0, 1)$ (that is, $H = K = 1$ and noise covariance $R = 0$), the mutual information of the joint law is infinite:

$$I(X; Y) = \infty,$$

while the log-determinant expression evaluates to

$$\frac{1}{2 \ln 2} \ln \frac{\det(0 + 1 \cdot 1 \cdot 1)}{\det 0} = 0$$

under the conventions $x / 0 = 0$ and $\ln 0 = 0$.
