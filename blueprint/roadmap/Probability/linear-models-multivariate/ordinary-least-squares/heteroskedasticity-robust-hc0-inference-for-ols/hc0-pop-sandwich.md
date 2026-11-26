# Population HC0 sandwich

Let $x_0$ be a random vector in $\mathbb{R}^p$ and $u_0$ a real random variable on a measure space $(\Omega, \mu)$, with population Gram matrix $Q = \big(\int x_{0,a} x_{0,b}\, d\mu\big)_{ab}$ and population HC0 meat $\Omega = \big(\int u_0^2 x_{0,a} x_{0,b}\, d\mu\big)_{ab}$ (integrals of non-integrable functions taken to be $0$). The population HC0 sandwich is

$$V = Q^{-1}\, \Omega\, \big(Q^{-1}\big)^\top,$$

where the inverse of a singular matrix is taken to be the zero matrix; it is the asymptotic covariance of $\sqrt{n}(\hat\beta_n - \beta)$ in the random-design linear model.
