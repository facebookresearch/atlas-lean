# Kl Div comp Prod noise Kernel output Moments

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. Let $\rho$ be a probability measure on $\mathbb{R}^\kappa$ with finite second moment, mean $m$ and covariance matrix $K$ ($K_{ab} = \operatorname{Cov}_\rho(x_a, x_b)$). Let $N_H$ be the Gaussian noise kernel sending $x$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Then the Kullback–Leibler divergence, in nats, of the joint law $\rho \otimes N_H$ from $\rho$ times the moment-matched Gaussian reference is

$$D_{\mathrm{KL}}\!\left(\rho \otimes N_H \,\middle\|\, \rho \times \mathcal{N}(Hm,\, HKH^\top + R)\right) = \frac{1}{2}\ln\frac{\det(R + HKH^\top)}{\det R}.$$
