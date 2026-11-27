# Conditional law of the channel output

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$. Then the conditional distribution of $Y = HX + Z$ given $X$ agrees, for $X_\ast\mu$-almost every $x$, with the additive-noise kernel at $x$:

$$P_{Y \mid X = x} = \text{law of } Hx + Z' \text{ with } Z' \sim \mathcal{N}(0, R).$$

$\mathcal{N}(m, S)$ is Mathlib's Gaussian with mean $m$ and covariance parameter $S$, which is the point mass $\delta_m$ when $S$ is not positive semidefinite; the statement holds for every real matrix $R$.
