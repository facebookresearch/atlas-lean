# Chow–Liu product approximation of a joint law

Let $\iota$ be a finite set of variables, $P$ a probability mass function on $\prod_i \alpha_i$ (the joint law of
$X = (X_i)_i$) and $\tau$ a dependence forest with parent map $j$. Chow–Liu's product approximation is

$$P_\tau(x) = \prod_{i} P(x_i \mid x_{j(i)}),$$

with the marginal $P(x_i)$ for a parentless $i$. The conditional $P(x_i \mid x_j)$ is
$P(x_i, x_j) / P(x_j)$, computed from the marginals of $P$; where $P(x_j) = 0$ the quotient is $0$, and such
$x$ have $P(x) = 0$.
