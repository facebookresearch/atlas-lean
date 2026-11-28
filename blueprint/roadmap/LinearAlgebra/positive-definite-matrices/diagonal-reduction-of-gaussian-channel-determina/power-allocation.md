# Power allocation of an input covariance

Let $m$, $n$ be finite index sets, $H \in \mathbb{R}^{m \times n}$ a real matrix and $R \in \mathbb{R}^{m \times m}$ positive definite. Write $G = H^{\top} R^{-1} H$ for the channel Gram matrix, $\lambda_i$ ($i \in n$) for its eigenvalues and $V$ for the orthogonal matrix of eigenvectors chosen by the spectral theorem, so that $G = V \operatorname{diag}(\lambda) V^{\top}$. For $K \in \mathbb{R}^{n \times n}$, the power allocation is the vector $p \in \mathbb{R}^n$ of diagonal entries of the rotated covariance: $p_i = (V^{\top} K V)_{ii}$.
