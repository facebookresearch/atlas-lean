# Positivity of the single-effect regression evidence

Let $I$ and $\iota$ be finite sets, let $w$ be [prior weights](prior-weights.md) on $\iota$, let $\sigma^2, \sigma_0^2$ be nonnegative reals with $\sigma^2 \ne 0$, let $X : \iota \to \mathbb{R}^I$ with $X_k \ne 0$ for every $k$, and let $y \in \mathbb{R}^I$. Then

$$\sum_{k \in \iota} w_k\, \mathrm{ABF}\bigl(s^2(\sigma^2, X_k), \sigma_0^2, \hat\beta(X_k, y)\bigr) > 0,$$

where $\mathrm{ABF}$ is [Wakefield's approximate Bayes factor](wakefield-abf.md), $\hat\beta$ the [least-squares effect estimate](ols-effect.md) and $s^2$ its [sampling variance](ols-var.md).
