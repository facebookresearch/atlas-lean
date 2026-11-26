# Mean fitness of a multivariate normal trait

Let $\iota$ be a finite set of traits. For a fitness function $W : \mathbb{R}^\iota \to \mathbb{R}$, a real $\iota \times \iota$ matrix $P$ and a mean vector $\mu \in \mathbb{R}^\iota$, the mean fitness is

$$\bar w(\mu) = \int W(z) \, dN(\mu, P)(z),$$

where $N(\mu, P)$ is the image of the standard Gaussian measure under $x \mapsto \mu + P^{1/2} x$: the multivariate normal distribution with mean $\mu$ and covariance $P$ when $P$ is positive semidefinite, and the point mass at $\mu$ otherwise, with the convention that the integral of a non-integrable function is $0$.
