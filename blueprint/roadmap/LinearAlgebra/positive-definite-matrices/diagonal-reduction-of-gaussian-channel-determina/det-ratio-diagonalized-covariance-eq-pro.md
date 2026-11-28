# Determinant ratio of the diagonalized covariance

Let $m$, $n$ be finite index sets, $H \in \mathbb{R}^{m \times n}$ a real matrix and $R \in \mathbb{R}^{m \times m}$ positive definite. Write $G = H^{\top} R^{-1} H$ for the channel Gram matrix, $\lambda_i$ ($i \in n$) for its eigenvalues and $V$ for the orthogonal matrix of eigenvectors chosen by the spectral theorem, so that $G = V \operatorname{diag}(\lambda) V^{\top}$. For a matrix $K \in \mathbb{R}^{n \times n}$ let $p_i = (V^{\top} K V)_{ii}$ and $K' = V \operatorname{diag}(p) V^{\top}$, and let $\rho(K) = \det(R + H K H^{\top}) / \det R$. If $K$ is positive semidefinite, then

$$\rho(K') = \prod_{i \in n} (1 + \lambda_i p_i).$$
