# Restricted log-likelihood of an error contrast

Let $A$ be a real $r \times n$ matrix, $V$ a real $n \times n$ matrix and $y \in \mathbb{R}^n$. The restricted (REML) log-likelihood is

$$\ell_A(V; y) = \log \varphi_{A V A^\top}(A y),$$

where $\varphi_S(z) = (2\pi)^{-r/2} (\det S)^{-1/2} \exp\!\big(-\tfrac12 z^\top S^{-1} z\big)$ is the centered Gaussian density with covariance $S$, evaluated with the conventions $\sqrt{t} = 0$ for $t < 0$, $1/0 = 0$, $S^{-1} = 0$ for singular $S$ and $\log 0 = 0$. In particular $\ell_A(V; y) = 0$ when $\det(A V A^\top) \le 0$.
