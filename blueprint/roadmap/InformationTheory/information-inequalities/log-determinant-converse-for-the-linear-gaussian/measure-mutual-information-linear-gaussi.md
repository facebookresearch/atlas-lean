# All-law log-det converse for the linear Gaussian channel

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$, and suppose $X$ satisfies the power constraint with budget $P$: $P \ge 0$ and $\mathbb{E}\lVert X \rVert^2 \le P$. Let $K$ be the covariance matrix of $X$, $K_{ab} = \operatorname{Cov}_\mu(X_a, X_b)$, and let $Y = HX + Z$. Then $K$ is positive semidefinite, $\operatorname{tr} K \le P$, and the mutual information of the joint law of $(X, Y)$, in bits, satisfies

$$I(X; Y) \le \max\left\{\frac{1}{2\ln 2}\ln\frac{\det(R + HKH^\top)}{\det R},\ 0\right\}.$$

The input $X$ need not be Gaussian or centered.
