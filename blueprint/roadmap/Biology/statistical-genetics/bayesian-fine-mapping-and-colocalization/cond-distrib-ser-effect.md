# The effect posterior of the single-effect regression

Let $I$ be a finite index set and let $P$ be a probability measure on a measurable space $\Omega$. Let $\beta : \Omega \to \mathbb{R}$ and $e : \Omega \to \mathbb{R}^I$ be measurable and independent under $P$, and let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$. Suppose that $\beta$ has law $N(0, \sigma_0^2)$ and $e$ has law $N(0, \sigma^2 \mathrm{I})$ under $P$, and let $x \in \mathbb{R}^I$ with $x \ne 0$. Put $Y = x \beta + e$. Then for almost every $y$ with respect to the law of $Y$, the conditional distribution of $\beta$ given $Y = y$ is the normal distribution (Wang et al. 2020)

$$N\Bigl(\frac{\sigma_0^2}{\sigma_0^2 + s^2}\, \hat\beta,\ \frac{\sigma_0^2 s^2}{\sigma_0^2 + s^2}\Bigr),$$

where $\hat\beta = x^\top y / x^\top x$ is the [least-squares effect estimate](ols-effect.md) and $s^2 = \sigma^2 / x^\top x$ its [sampling variance](ols-var.md).

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, M. Stephens, *A simple new approach to variable selection in regression, with application to genetic fine mapping*, J. R. Stat. Soc. B 82 (2020), 1273–1300.
