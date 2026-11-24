# Lande's gradient of mean fitness for multivariate traits

Let $\iota$ be a finite set of traits, $W : \mathbb{R}^\iota \to \mathbb{R}$ measurable and bounded, and $P$ a positive definite real $\iota \times \iota$ matrix. Then for every $\mu \in \mathbb{R}^\iota$ the [mean fitness](mean-fitness-mv.md) is differentiable at $\mu$ with gradient

$$\nabla \bar w(\mu) = P^{-1} \int W(z)\, (z - \mu) \, dN(\mu, P)(z).$$
