# Log-determinant converse for the linear Gaussian channel

Let $\kappa$ and $\iota$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. On a probability space, let $X$ and $Z$ be measurable random vectors in $\mathbb{R}^\kappa$ and $\mathbb{R}^\iota$, independent, with $Z \sim \mathcal{N}(0, R)$, and let $Y = HX + Z$. Suppose $P \ge 0$ and $\mathbb{E}\|X\|^2 \le P$ (as a lower integral), and let $K_{ab} = \operatorname{Cov}(X_a, X_b)$. Then $K$ is positive semidefinite, $\operatorname{tr} K \le P$, and the mutual information in bits satisfies

$$I(X; Y) \le \max\left\{0,\ \frac{\log\big(\det(R + H K H^{\mathsf T}) / \det R\big)}{2 \log 2}\right\}.$$
