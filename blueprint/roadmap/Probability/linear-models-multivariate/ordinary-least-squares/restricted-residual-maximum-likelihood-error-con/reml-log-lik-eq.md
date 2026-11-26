# Closed form of the restricted log-likelihood

Let $A$ be a real $r \times n$ matrix, $V$ a real $n \times n$ matrix with $S = A V A^\top$ positive definite, and $y \in \mathbb{R}^n$. Then the restricted log-likelihood $\ell_A(V; y) = \log \varphi_S(A y)$ is

$$\ell_A(V; y) = -\frac{r}{2}\log(2\pi) - \frac12 \log\det S - \frac12 (A y)^\top S^{-1} (A y).$$
