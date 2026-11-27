# Asymptotic normality of roots of a vector estimating equation

Let $X_0, X_1, \dots$ be mutually independent observations with law $\mu$ on a probability space and $\psi_\theta(x) \in E$ an estimating function ($E$ a finite-dimensional real inner product space) with $\psi_{\theta_0}$ measurable, $\int\|\psi_{\theta_0}\|^2d\mu < \infty$ and $\int\psi_{\theta_0}d\mu = 0$. Assume that for some $\delta > 0$, $\theta \mapsto \psi_\theta(x)$ is differentiable on $B(\theta_0, \delta)$ with $\|D\psi_\theta(x) - D\psi_{\theta_0}(x)\| \le M(x)\|\theta - \theta_0\|$ for a measurable integrable $M$, $D\psi_{\theta_0}$ is strongly measurable and integrable, and $D = \int D\psi_{\theta_0}d\mu$ is invertible. Let $\hat\theta_n$ be almost everywhere measurable, solve $\sum_{i<n}\psi_{\hat\theta_n}(X_i) = 0$ with probability tending to $1$ and converge to $\theta_0$ in probability. If $Y$ is a random vector with $\langle Y, t\rangle \sim \mathcal N(0, \int\langle\psi_{\theta_0}, t\rangle^2d\mu)$, then $\sqrt n(\hat\theta_n - \theta_0)$ converges in distribution to $-D^{-1}Y$.

## Sources

- van der Vaart (1998), Theorem 5.41; Lehmann & Casella (1998), Theorem 6.5.1.
