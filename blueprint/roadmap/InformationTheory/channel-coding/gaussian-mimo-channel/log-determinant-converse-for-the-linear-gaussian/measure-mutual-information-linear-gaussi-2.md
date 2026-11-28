# Measure Mutual Information linear Gaussian Channel le i Sup

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$, and suppose $X$ satisfies the power constraint $P \ge 0$, $\mathbb{E}\lVert X \rVert^2 \le P$. With $Y = HX + Z$, the mutual information in bits is at most the supremum of the log-determinant value over admissible covariances:

$$I(X; Y) \le \sup_{K' \succeq 0,\ \operatorname{tr} K' \le P} \max\left\{\frac{1}{2\ln 2}\ln\frac{\det(R + HK'H^\top)}{\det R},\ 0\right\}.$$
