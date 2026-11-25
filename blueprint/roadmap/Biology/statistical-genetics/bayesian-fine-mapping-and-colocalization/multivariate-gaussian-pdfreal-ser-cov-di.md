# The regression Bayes factor is the Wakefield ABF

Let $I$ be a finite index set, let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$, and let $x, y \in \mathbb{R}^I$ with $x \ne 0$. Write $\varphi_\Sigma(y) = (2\pi)^{-|I|/2} (\det \Sigma)^{-1/2} \exp(-\tfrac12 y^\top \Sigma^{-1} y)$ for the centred Gaussian density with covariance $\Sigma$. Then (Wang et al. 2020)

$$\frac{\varphi_{\sigma_0^2 x x^\top + \sigma^2 \mathrm{I}}(y)}{\varphi_{\sigma^2 \mathrm{I}}(y)} = \mathrm{ABF}\bigl(s^2(\sigma^2, x), \sigma_0^2, \hat\beta(x, y)\bigr),$$

where $\hat\beta(x, y) = x^\top y / x^\top x$ is the [least-squares effect estimate](ols-effect.md), $s^2(\sigma^2, x) = \sigma^2 / x^\top x$ its [sampling variance](ols-var.md), and $\mathrm{ABF}$ is [Wakefield's approximate Bayes factor](wakefield-abf.md).

The left side is the density of the phenotype $y$ when the variant $x$ carries an $N(0, \sigma_0^2)$ effect, divided by its density when there is no effect.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, M. Stephens, *A simple new approach to variable selection in regression, with application to genetic fine mapping*, J. R. Stat. Soc. B 82 (2020), 1273–1300.
