# Measure Mutual Information two Point comp Prod noise Kernel le

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, $H \in \mathbb{R}^{\iota \times \kappa}$, $R \in \mathbb{R}^{\iota \times \iota}$ positive definite, and $c, a \in \mathbb{R}^\kappa$. Let $\rho = \tfrac{1}{2}\delta_{c+a} + \tfrac{1}{2}\delta_{c-a}$, a non-Gaussian law with mean $c$ and covariance $aa^\top$, and let $N_H$ be the Gaussian noise kernel sending $x$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Then the mutual information in bits satisfies the converse bound at $K = aa^\top$:

$$I(\rho \otimes N_H) \le \max\left\{\frac{1}{2\ln 2}\ln\frac{\det(R + H a a^\top H^\top)}{\det R},\ 0\right\}.$$
