# Translating a multivariate Gaussian

Let $\iota$ be a finite index set. For all
$c, \mu \in \mathbb{R}^\iota$ and every real $\iota \times \iota$ matrix $S$, the pushforward of
$N(\mu, S)$ under the translation $x \mapsto c + x$ is $N(c + \mu, S)$.

No positive semidefiniteness is assumed: when $S$ is not positive semidefinite, $N(\mu, S)$ is
taken to be the point mass at $\mu$.

For example, for a real matrix $H$, a point $x$ and any real $\iota \times \iota$ matrix $R$, the law of $Hx + Z$ with $Z \sim N(0, R)$ is $N(Hx, R)$ (take $c = Hx$, $\mu = 0$ and $S = R$); this is the additive-noise channel kernel at input $x$.
