# Conditioning on a signal observed in independent additive noise

Let $E$ be a nonempty
standard Borel space that is an abelian group with measurable addition, let $F$ be a measurable
space, and let $Y \colon \Omega \to F$ and $Z \colon \Omega \to E$ be independent measurable random
variables on a probability space. For every measurable $f \colon F \to E$ and almost every $y$
with respect to the law of $Y$, the conditional distribution of $f(Y) + Z$ given $Y = y$ is the
law of $f(y) + Z$.

For example, for the linear Gaussian channel, with $Y = X$ an input in $\mathbb{R}^\kappa$, $f(x) = Hx$ for a real $\iota \times \kappa$ matrix $H$ and $Z \sim \mathcal{N}(0, R)$ on $\mathbb{R}^\iota$, the conditional law of the output $HX + Z$ given $X = x$ is the law of $Hx + Z$, for almost every $x$ under the law of $X$.
