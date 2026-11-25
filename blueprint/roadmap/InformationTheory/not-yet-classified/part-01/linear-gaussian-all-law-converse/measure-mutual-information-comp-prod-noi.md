# Log-determinant bound on mutual information for every input law

Let $\kappa$ and $\iota$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $W_R$ be the channel that maps an input $x \in \mathbb{R}^\kappa$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Mutual information is measured in bits, $I(\mu) = D_{\mathrm{KL}}(\mu \,\|\, \mu_X \otimes \mu_Y)/\ln 2$.

Let $\rho$ be a probability measure on $\mathbb{R}^\kappa$ with finite second moment (any mean, not necessarily Gaussian), with covariance matrix $K_{ab} = \operatorname{Cov}_\rho(x_a, x_b)$. Then the joint law $\rho \otimes W_R$ of input and output satisfies

$$I(\rho \otimes W_R) \le \max\left\{0,\ \frac{\log\big(\det(R + H K H^{\mathsf T}) / \det R\big)}{2 \log 2}\right\}.$$
