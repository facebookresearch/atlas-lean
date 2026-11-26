# Log-likelihood ratio of the Gaussian channel joint law

Let $\kappa$ and $\iota$ be finite index sets, let $H$ be a real $\iota \times \kappa$ matrix acting as a linear map $\mathbb{R}^\kappa \to \mathbb{R}^\iota$, let $q \in \mathbb{R}^\iota$, and let $R, T$ be real $\iota\times\iota$ matrices. Assume $R$ and $T$ are positive definite, and let $\mu$ be a probability measure on $\mathbb{R}^\kappa$. Let $k$ be the Gaussian noise kernel $x \mapsto \mathcal N(Hx, R)$ (the law of $Hx + Z$ with $Z \sim \mathcal N(0, R)$), and let $P = \mu \otimes k$ be the joint law of the input $x \sim \mu$ and the output $y \sim k(x)$ on $\mathbb{R}^\kappa \times \mathbb{R}^\iota$, and $Q_0 = \mu \otimes \mathcal N(q, T)$ the product law. Then the log-likelihood ratio $\log \frac{dP}{dQ_0}$ satisfies, for $P$-almost every $(x, y)$,

$$\log \frac{dP}{dQ_0}(x, y) = \frac{1}{2}\left( \log\frac{\det T}{\det R} - (y - Hx)^{\top} R^{-1} (y - Hx) + (y - q)^{\top} T^{-1} (y - q) \right).$$
