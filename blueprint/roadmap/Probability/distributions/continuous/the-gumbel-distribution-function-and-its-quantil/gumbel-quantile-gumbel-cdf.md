# The Gumbel quantile inverts the distribution function

Let $\mu, \beta \in \mathbb{R}$ with $\beta \ne 0$, and let $F_{\mu,\beta}(x) = \exp(-\exp(-(x - \mu)/\beta))$ and $Q_{\mu,\beta}(q) = \mu - \beta \log(-\log q)$. For every $x \in \mathbb{R}$,

$$Q_{\mu,\beta}\big(F_{\mu,\beta}(x)\big) = x.$$

For a scale $\beta > 0$, $F_{\mu,\beta}$ is the distribution function of the Gumbel distribution with location $\mu$ and scale $\beta$, and $Q_{\mu,\beta}$ restricted to $0 < q < 1$ is its quantile function. For $\beta < 0$ both functions are decreasing, so they are not a distribution function and its quantile, although the inversion identity still holds.
