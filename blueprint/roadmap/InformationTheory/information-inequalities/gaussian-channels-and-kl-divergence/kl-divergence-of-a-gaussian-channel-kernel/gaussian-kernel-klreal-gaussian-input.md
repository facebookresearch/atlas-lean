# Closed form of the Gaussian kernel divergence for a Gaussian input

Let $\kappa$ and $\iota$ be finite index sets, let $H$ be a real $\iota \times \kappa$ matrix acting as a linear map $\mathbb{R}^\kappa \to \mathbb{R}^\iota$, let $q \in \mathbb{R}^\iota$, and let $R, T$ be real $\iota\times\iota$ matrices. For a probability measure $\mu$ on $\mathbb{R}^\kappa$, write

$$F(\mu) = \frac{1}{2}\left( \log\frac{\det T}{\det R} - |\iota| + \operatorname{tr}(T^{-1} R) + \int (Hx - q)^{\top} T^{-1} (Hx - q)\, d\mu(x) \right).$$

Let $m \in \mathbb{R}^\kappa$ and let $S$ be a positive semidefinite $\kappa\times\kappa$ matrix. Then

$$F\bigl(\mathcal N(m, S)\bigr) = \frac{1}{2}\left( \log\frac{\det T}{\det R} - |\iota| + \operatorname{tr}(T^{-1} R) + \operatorname{tr}\bigl(T^{-1} H S H^{\top}\bigr) + (Hm - q)^{\top} T^{-1} (Hm - q) \right).$$

No assumption on $R$ or $T$ is made; $T^{-1}$, $\log$ and the division follow the conventions (the inverse of a singular matrix is $0$, $x/0 = 0$, $\log 0 = 0$, $\log x = \log|x|$ for $x < 0$).
