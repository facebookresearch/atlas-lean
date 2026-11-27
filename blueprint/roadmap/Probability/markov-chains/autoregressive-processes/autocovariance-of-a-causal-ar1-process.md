# Autocovariance of the causal AR(1) process

Let $(\varepsilon_t)_{t \in \mathbb{Z}}$ be i.i.d. with mean $0$ and variance $\sigma^2 > 0$, and $|\phi| < 1$. The series $X_t = \sum_{j \ge 0}\phi^j\varepsilon_{t-j}$ converges in $L^2$ and almost surely and solves $X_t = \phi X_{t-1} + \varepsilon_t$. Its autocovariance is $\operatorname{Cov}(X_t, X_{t+h}) = \sigma^2\phi^{|h|}/(1 - \phi^2)$ for every integer $h$, since covariance is continuous in $L^2$ and $\operatorname{Cov}(\sum_j \phi^j\varepsilon_{t-j}, \sum_k \phi^k\varepsilon_{t+h-k}) = \sigma^2\sum_{j \ge 0}\phi^j\phi^{j+h}$ for $h \ge 0$. The law of $(X_t)$ is stationary; the uniqueness of the causal stationary solution is a separate statement.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- $L^2$ and almost-sure convergence of the moving-average representation of the causal AR(1) solution.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
