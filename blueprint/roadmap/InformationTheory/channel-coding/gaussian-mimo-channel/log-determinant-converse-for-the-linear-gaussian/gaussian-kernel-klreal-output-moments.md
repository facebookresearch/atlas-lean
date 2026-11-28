# Gaussian Kernel KLReal output Moments

Let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. Let $\rho$ be a probability measure on $\mathbb{R}^\kappa$ with finite second moment, mean $m$ and covariance matrix $K$ ($K_{ab} = \operatorname{Cov}_\rho(x_a, x_b)$). For an output reference with mean $q \in \mathbb{R}^\iota$ and covariance $T$, the closed-form expression, which is the Gaussian kernel divergence when $T$ is positive definite and only an algebraic expression otherwise, is

$$G(q, T) = \frac{1}{2}\left(\ln\frac{\det T}{\det R} - \lvert\iota\rvert + \operatorname{tr}(T^{-1}R) + \int (Hx - q)^\top T^{-1} (Hx - q)\, d\rho(x)\right).$$

At the moment-matched reference $q = Hm$, $T = HKH^\top + R$, the trace terms cancel the dimension and

$$G(Hm,\, HKH^\top + R) = \frac{1}{2}\ln\frac{\det(R + HKH^\top)}{\det R}.$$
