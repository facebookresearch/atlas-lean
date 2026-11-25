# Log-determinant bound for a two-point input law

Let $\kappa$ and $\iota$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $W_R$ be the channel that maps an input $x \in \mathbb{R}^\kappa$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Mutual information is measured in bits, $I(\mu) = D_{\mathrm{KL}}(\mu \,\|\, \mu_X \otimes \mu_Y)/\ln 2$.

Let $c, a \in \mathbb{R}^\kappa$ and let $\rho = \tfrac12 \delta_{c+a} + \tfrac12 \delta_{c-a}$. Then

$$I(\rho \otimes W_R) \le \max\left\{0,\ \frac{\log\big(\det(R + H a a^{\mathsf T} H^{\mathsf T}) / \det R\big)}{2 \log 2}\right\}.$$
