# Gaussian channel joint law is absolutely continuous

Let $\kappa$ and $\iota$ be finite index sets, let $H$ be a real $\iota \times \kappa$ matrix acting as a linear map $\mathbb{R}^\kappa \to \mathbb{R}^\iota$, let $q \in \mathbb{R}^\iota$, and let $R, T$ be real $\iota\times\iota$ matrices. Assume $R$ and $T$ are positive definite, and let $\mu$ be a probability measure on $\mathbb{R}^\kappa$. Let $k$ be the Gaussian noise kernel $x \mapsto \mathcal N(Hx, R)$ (the law of $Hx + Z$ with $Z \sim \mathcal N(0, R)$), and let $P = \mu \otimes k$ be the joint law of the input $x \sim \mu$ and the output $y \sim k(x)$ on $\mathbb{R}^\kappa \times \mathbb{R}^\iota$, and $Q_0 = \mu \otimes \mathcal N(q, T)$ the product law. Then

$$P \ll Q_0.$$
