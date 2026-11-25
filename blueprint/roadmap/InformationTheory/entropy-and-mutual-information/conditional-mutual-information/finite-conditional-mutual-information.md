# Conditional mutual information of a finite joint law

Let $\alpha, \beta, \gamma$ be finite sets and $p$ a probability mass function on $\alpha \times \beta \times \gamma$, the joint law of $(X, Y, Z)$, with marginals $p(x, z)$, $p(y, z)$, $p(z)$; entropies and mutual informations are in bits.
The conditional mutual information of $X$ and $Y$ given $Z$ is

$$I(X; Y \mid Z) = \sum_{x, y, z} p(x, y, z) \log_2 \frac{p(x, y, z)\, p(z)}{p(x, z)\, p(y, z)},$$

the terms with $p(x, y, z) = 0$ being $0$ (when $p(x, y, z) > 0$ all the marginals in the quotient are positive).
