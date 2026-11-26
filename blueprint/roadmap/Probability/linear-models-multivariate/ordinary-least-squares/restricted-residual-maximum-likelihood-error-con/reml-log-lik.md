# Restricted log-likelihood of an error contrast

Let $A$ be a real $r \times n$ matrix, $V$ a real $n \times n$ matrix and $y \in \mathbb{R}^n$. The restricted (REML) log-likelihood is

$$\ell_A(V; y) = \log \varphi_{A V A^\top}(A y),$$

where $\varphi_S(z) = (2\pi)^{-r/2} (\det S)^{-1/2} \exp\!\big(-\tfrac12 z^\top S^{-1} z\big)$ is the formula of the centered Gaussian density with covariance $S$, evaluated with the conventions $\sqrt{t} = 0$ for $t < 0$, $1/0 = 0$, $S^{-1} = 0$ for singular $S$ and $\log 0 = 0$. In particular $\ell_A(V; y) = 0$ when $\det(A V A^\top) \le 0$.

When $S = A V A^\top$ is positive definite (for example when $V$ is positive definite and $A A^\top$ is invertible), $\varphi_S$ is the Lebesgue density of $N(0, S)$, which is the law of the contrast $A y$ when $y \sim N(X\beta, V)$ and $A$ is an error contrast for $X$ ([density of the error contrast](has-law-error-contrast-with-density.md)). For other $A$ and $V$ the expression is only defined by the conventions above and is not a log density: with $A = 0$ and $V = I$, the contrast $A y = 0$ has a point-mass law, which has no Lebesgue density.
