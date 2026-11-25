# Posterior inclusion probabilities of the single-effect regression

Let $I$ and $\iota$ be finite sets, let $w$ be [prior weights](prior-weights.md) on $\iota$, let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$, let $X : \iota \to \mathbb{R}^I$ with $X_k \ne 0$ for every $k$, and let $y \in \mathbb{R}^I$ and $j \in \iota$. Write $\varphi_k(y)$ for the centred Gaussian density at $y$ with covariance $\sigma_0^2 X_k X_k^\top + \sigma^2 \mathrm{I}$. Then (Wang et al. 2020)

$$\frac{w_j\, \varphi_j(y)}{\sum_{k \in \iota} w_k\, \varphi_k(y)} = \mathrm{PIP}_j(w, \mathrm{BF}), \qquad \mathrm{BF}_k = \mathrm{ABF}\bigl(s^2(\sigma^2, X_k), \sigma_0^2, \hat\beta(X_k, y)\bigr),$$

where $\mathrm{PIP}$ is the [posterior inclusion probability](pip.md), $\mathrm{ABF}$ is [Wakefield's approximate Bayes factor](wakefield-abf.md), $\hat\beta$ the [least-squares effect estimate](ols-effect.md) and $s^2$ its [sampling variance](ols-var.md).

The left side is Bayes' rule for the causal variant: the posterior probability that variant $j$ carries the single effect, given the phenotype $y$.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, M. Stephens, *A simple new approach to variable selection in regression, with application to genetic fine mapping*, J. R. Stat. Soc. B 82 (2020), 1273–1300.
