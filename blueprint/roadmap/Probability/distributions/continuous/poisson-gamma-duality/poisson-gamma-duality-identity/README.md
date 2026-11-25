# Poisson–Gamma duality

Let $k \in \mathbb{N}$, $r > 0$ and $x \ge 0$, and let $X$ have the gamma law with shape $k + 1$ and rate $r$. Then $P(X > x) = F_k(rx) = \sum_{j=0}^{k} e^{-rx} (rx)^j / j!$, where $F_k(\lambda)$, the Poisson distribution function, is the probability that a Poisson variable with mean $\lambda$ is at most $k$.

## Idea

In a Poisson process of rate $r$, the time of the $(k+1)$-st point has the gamma law with shape $k + 1$ and rate $r$. The number of points in $[0, x]$ is Poisson with mean $rx$. The $(k+1)$-st point comes after time $x$ exactly when at most $k$ points fall in $[0, x]$, so the two probabilities agree. Analytically, the identity is the Erlang tail formula, obtained by integrating the gamma tail by parts $k$ times. The duality turns statements about Poisson counts into statements about gamma tails and back. Seen as a function of the mean, $F_k$ is continuous and strictly decreasing from $1$ to $0$, which is what exact Poisson confidence bounds use.

## Statements

- [Poisson–Gamma duality](gamma-measure-real-ioi-poisson-cdf.md)
- [Poisson distribution function as a function of the mean](poisson-cdf.md): definition used in the main statement
- [Poisson distribution function agrees with the Poisson law](poisson-measure-real-iic.md): basic property: agreement with the Poisson law
- [Poisson distribution function at mean zero](poisson-cdf-zero-left.md): basic property: mean zero
- [Poisson distribution function at count zero](poisson-cdf-zero-right.md): basic property: count zero
- [Positivity of the Poisson distribution function](poisson-cdf-pos.md): basic property: positivity
- [Poisson distribution function is monotone in the count](poisson-cdf-mono.md): basic property: monotone in the count
- [Poisson distribution function is strictly increasing in the count](poisson-cdf-lt-poisson-cdf-succ.md): basic property: strictly increasing in the count when the mean is positive
- [Derivative of the Poisson distribution function in the mean](has-deriv-at-poisson-cdf.md): basic property: derivative in the mean
- [Continuity of the Poisson distribution function in the mean](continuous-poisson-cdf.md): basic property: continuity in the mean
- [Poisson distribution function is strictly decreasing in the mean](poisson-cdf-strict-anti-on.md): basic property: strictly decreasing in the mean
- [Poisson distribution function vanishes as the mean grows](tendsto-poisson-cdf-at-top.md): basic property: limit as the mean grows
- [Poisson distribution function tends to one as the count grows](tendsto-poisson-cdf-nat.md): basic property: limit as the count grows

## Background

- [Upper incomplete gamma function and the gamma tail](../../gamma-distribution/incomplete-gamma-tail/README.md)
