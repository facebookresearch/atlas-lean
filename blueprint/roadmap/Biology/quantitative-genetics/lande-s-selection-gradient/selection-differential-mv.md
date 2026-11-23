# Multivariate directional selection differential

Let $\iota$ be a finite set of traits. For a fitness function $W : \mathbb{R}^\iota \to \mathbb{R}$, a real $\iota \times \iota$ matrix $P$ and $\mu \in \mathbb{R}^\iota$, the directional selection differential is the vector

$$S = \bar w(\mu)^{-1} \int W(z)\, (z - \mu) \, dN(\mu, P)(z),$$

where $\bar w$ is the [mean fitness](mean-fitness-mv.md) and $N(\mu, P)$ the Gaussian measure defined there, with the convention $0^{-1} = 0$.
