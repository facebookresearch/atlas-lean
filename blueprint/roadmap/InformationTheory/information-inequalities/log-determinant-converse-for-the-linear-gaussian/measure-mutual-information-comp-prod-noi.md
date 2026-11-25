# Law-level all-law converse

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. Let $\rho$ be any probability measure on $\mathbb{R}^\kappa$ with finite second moment (any mean, not necessarily Gaussian) and covariance matrix $K$ ($K_{ab} = \operatorname{Cov}_\rho(x_a, x_b)$). Let $N_H$ be the Gaussian noise kernel sending $x$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Then the mutual information of the joint law $\rho \otimes N_H$, in bits, satisfies

$$I(\rho \otimes N_H) \le \max\left\{\frac{1}{2\ln 2}\ln\frac{\det(R + HKH^\top)}{\det R},\ 0\right\}.$$
