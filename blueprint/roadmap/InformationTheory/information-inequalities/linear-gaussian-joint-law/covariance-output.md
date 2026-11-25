# Output covariance

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$ positive semidefinite. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$, and suppose $X$ has finite second moment and covariance matrix $K$, $K_{ab} = \operatorname{Cov}_\mu(X_a, X_b)$. Then for all $i, j \in \iota$,

$$\operatorname{Cov}_\mu\big((HX + Z)_i,\ (HX + Z)_j\big) = (HKH^\top + R)_{ij}.$$
