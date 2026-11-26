# Determinant ratio of a Gaussian channel

For finite index sets $m$, $n$ and real matrices $H \in \mathbb{R}^{m \times n}$, $R \in \mathbb{R}^{m \times m}$, $K \in \mathbb{R}^{n \times n}$, the determinant ratio is

$$\rho(K) = \frac{\det(R + H K H^{\top})}{\det R},$$

with the convention $x/0 = 0$. The definition places no condition on the matrices. Its information-theoretic meaning needs one: for the channel $Y = H X + Z$ with $X$ and $Z$ independent Gaussian vectors, input covariance $K$ positive semidefinite and noise covariance $R$ positive definite, the mutual information between $X$ and $Y$ is $\tfrac12 \log \rho(K)$, in nats with the natural logarithm and in bits with the logarithm to base $2$. Without positive definite noise this fails: for $Y = X$ with $X$ standard Gaussian ($H = K = 1$, $R = 0$) the mutual information is infinite, while the convention gives $\rho(K) = 0$.
