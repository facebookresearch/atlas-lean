# Diagonal reduction of the Gaussian channel determinant

Let $m$ and $n$ be finite index sets, $H \in \mathbb{R}^{m \times n}$, and $R \in \mathbb{R}^{m \times m}$ positive definite. Let $V$ be the orthogonal matrix of eigenvectors of $H^{\mathsf T} R^{-1} H$ given by the spectral theorem, with eigenvalues $\lambda_i$. For $K \in \mathbb{R}^{n \times n}$ let $p_i = (V^{\mathsf T} K V)_{ii}$ and $\tilde K = V \operatorname{diag}(p) V^{\mathsf T}$, and write $r(K) = \det(R + H K H^{\mathsf T}) / \det R$. If $K$ is positive semidefinite, then $\lambda_i \ge 0$ for every $i$, $\operatorname{tr} \tilde K = \operatorname{tr} K$, $r(K) \le r(\tilde K)$, and

$$r(\tilde K) = \prod_i (1 + \lambda_i p_i).$$
