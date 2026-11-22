# Single-effect likelihood-ratio identity

Let $I$ and $\iota$ be finite sets, let $w : \iota \to \mathbb{R}$ be arbitrary real weights, and let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$. Let $X : \iota \to \mathbb{R}^I$ assign to each variant a genotype vector with $X_k \ne 0$ for every $k$, and let $y \in \mathbb{R}^I$ and $j \in \iota$. Write $\varphi_k(y)$ for the centred Gaussian density at $y$ with the [single-effect regression covariance](ser-cov.md) $\sigma_0^2 X_k X_k^\top + \sigma^2 \mathrm{I}$, and

$$\mathrm{BF}_k = \mathrm{ABF}\bigl(s^2(\sigma^2, X_k), \sigma_0^2, \hat\beta(X_k, y)\bigr)$$

for the [Wakefield approximate Bayes factor](wakefield-abf.md) of the [least-squares estimate](ols-effect.md) with its [sampling variance](ols-var.md). Then

$$\frac{w_j\, \varphi_j(y)}{\sum_{k \in \iota} w_k\, \varphi_k(y)} = \frac{w_j \,\mathrm{BF}_j}{\sum_{k \in \iota} w_k \,\mathrm{BF}_k},$$

with the convention $x / 0 = 0$ on both sides. The right side is the [normalized weighted evidence](normalized-weighted-evidence.md); for arbitrary real weights it need not be a probability.
