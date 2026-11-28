# KL divergence of a Gaussian channel kernel

Let $\kappa$ and $\iota$ be finite index sets, let $H$ be a real $\iota \times \kappa$ matrix acting as a linear map $\mathbb{R}^\kappa \to \mathbb{R}^\iota$, let $q \in \mathbb{R}^\iota$, and let $R, T$ be real $\iota\times\iota$ matrices. Assume $\iota$ is nonempty and $R$, $T$ are positive definite, and let $\mu$ be a probability measure on $\mathbb{R}^\kappa$ with finite second moment ($\mathrm{id} \in L^2(\mu)$). Let $k$ be the Gaussian noise kernel $x \mapsto \mathcal N(Hx, R)$ (the law of $Hx + Z$ with $Z \sim \mathcal N(0, R)$), and let $P = \mu \otimes k$ be the joint law of the input $x \sim \mu$ and the output $y \sim k(x)$ on $\mathbb{R}^\kappa \times \mathbb{R}^\iota$, and $Q_0 = \mu \otimes \mathcal N(q, T)$ the product law. Then

$$\mathrm{KL}(P \,\|\, Q_0) = \operatorname{ofReal}\!\left( \frac{1}{2}\left( \log\frac{\det T}{\det R} - d + \operatorname{tr}(T^{-1} R) + \int (Hx - q)^{\top} T^{-1} (Hx - q)\, d\mu(x) \right)\right),$$

where $d = |\iota|$ and $\operatorname{ofReal}$ sends $r \in \mathbb{R}$ to $\max(r, 0) \in [0, \infty]$.
