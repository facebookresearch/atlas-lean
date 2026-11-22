# The marginal law of the phenotype given the causal variant

Let $I$ be a finite index set and let $P$ be a probability measure on a measurable space $\Omega$. Let $\beta : \Omega \to \mathbb{R}$ and $e : \Omega \to \mathbb{R}^I$ be measurable and independent under $P$, and let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$. Suppose that $\beta$ has law $N(0, \sigma_0^2)$ and $e$ has law $N(0, \sigma^2 \mathrm{I})$ under $P$. Then for every $x \in \mathbb{R}^I$, the law of $y = x \beta + e$ is the measure on $\mathbb{R}^I$ with density

$$y \mapsto (2\pi)^{-|I|/2} (\det \Sigma)^{-1/2} \exp\bigl(-\tfrac12\, y^\top \Sigma^{-1} y\bigr)$$

with respect to Lebesgue measure, where $\Sigma = \sigma_0^2 x x^\top + \sigma^2 \mathrm{I}$ is the [single-effect regression covariance](ser-cov.md).
