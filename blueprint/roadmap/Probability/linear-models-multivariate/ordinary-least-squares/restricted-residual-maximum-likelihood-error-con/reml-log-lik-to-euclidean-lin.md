# Restricted log-likelihood as a log density

Let $A$ be a real $r \times n$ matrix, $V$ a real $n \times n$ matrix and $y \in \mathbb{R}^n$. The restricted log-likelihood $\ell_A(V; y)$ equals $\log \varphi_{A V A^\top}(A y)$, the logarithm of the centered Gaussian density with covariance $A V A^\top$ at the contrast vector $A y$, with the conventions $\sqrt{t} = 0$ for $t < 0$, $1/0 = 0$, $S^{-1} = 0$ for singular $S$ and $\log 0 = 0$.
