# Asymptotic normality of ordinary least squares

Let $(x_i, u_i)_{i \ge 0}$ be pairs of a regressor vector $x_i \in \mathbb{R}^k$ and a real error $u_i$ on a probability space, with responses $y_i = x_i^\top\beta + u_i$. Write $\hat Q_n = \frac1n\sum_{i<n} x_i x_i^\top$ for the sample Gram matrix, $Q = \mathbb{E}[x_0 x_0^\top]$ for the population Gram matrix, $\hat\beta_n = \hat Q_n^{-1}\,\frac1n\sum_{i<n} x_i y_i$ for the least-squares estimate from the first $n$ observations (with $\hat Q_n^{-1} = 0$ when $\hat Q_n$ is singular), and $\Omega = \mathbb{E}[u_0^2 x_0 x_0^\top]$. Assume the pairs $(x_i, u_i)$ are mutually independent and identically distributed, the products $x_{0a}x_{0b}$ are integrable, the score $u_0x_0$ is square integrable with $\mathbb{E}[u_0x_0] = 0$, and $Q$ is invertible. Then

$$\sqrt n\,(\hat\beta_n - \beta) \xrightarrow{d} \mathcal N\big(0,\ Q^{-1}\Omega Q^{-1}\big).$$
