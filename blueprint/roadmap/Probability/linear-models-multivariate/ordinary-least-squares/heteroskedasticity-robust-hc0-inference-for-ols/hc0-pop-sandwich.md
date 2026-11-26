# Population HC0 sandwich

Let $x_0$ be a random vector in $\mathbb{R}^p$ and $u_0$ a real random variable on a measure space $(\Omega, \mu)$, with population Gram matrix $Q = \big(\int x_{0,a} x_{0,b}\, d\mu\big)_{ab}$ and population HC0 meat $\Omega = \big(\int u_0^2 x_{0,a} x_{0,b}\, d\mu\big)_{ab}$ (integrals of non-integrable functions taken to be $0$). The population HC0 sandwich is

$$V = Q^{-1}\, \Omega\, \big(Q^{-1}\big)^\top,$$

where the inverse of a singular matrix is taken to be the zero matrix.

In the random-design linear model $y_i = x_i^\top\beta + u_i$, $V$ is the asymptotic covariance of the least-squares estimator under the assumptions of the central limit theorem for it: $\mu$ is a probability measure, the pairs $(x_i, u_i)$ are independent and identically distributed as $(x_0, u_0)$, the entries of $x_0x_0^\top$ are integrable, the score $u_0x_0$ is square integrable with $\int u_0x_0\,d\mu = 0$, and $Q$ is invertible. Then $\sqrt{n}(\hat\beta_n - \beta)$ converges in distribution to $N(0, V)$. Without these assumptions the matrix need not describe any limit: with one regressor and $x_i = u_i = 1$ for every $i$, $V = 1$, but $\hat\beta_n = \beta + 1$ and $\sqrt{n}(\hat\beta_n - \beta)$ diverges.
