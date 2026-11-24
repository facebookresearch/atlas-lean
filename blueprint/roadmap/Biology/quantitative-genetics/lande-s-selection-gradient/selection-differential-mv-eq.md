# Lande's equation for multivariate traits

Let $\iota$ be a finite set of traits, $W : \mathbb{R}^\iota \to \mathbb{R}$ measurable and bounded, $P$ a positive definite real $\iota \times \iota$ matrix, and $\mu \in \mathbb{R}^\iota$ with $\bar w(\mu) \ne 0$, where $\bar w$ is the [mean fitness](mean-fitness-mv.md). Then the [selection differential](selection-differential-mv.md) is

$$S = P\, \nabla \log \bar w(\mu),$$

with $\log x = \log|x|$ for $x < 0$; for $\bar w(\mu) > 0$ it is the covariance matrix applied to the gradient of log mean fitness at $\mu$ (Lande 1979).

## Sources

- R. Lande, *Quantitative genetic analysis of multivariate evolution, applied to brain:body size allometry*, Evolution 33 (1979), 402–416.
