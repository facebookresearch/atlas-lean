# Smoothed class probability is a Gaussian probability

Let $\iota$ be a finite index type, $Y$ a measurable space in which singletons are measurable, and $f : \mathbb{R}^\iota \to Y$ a measurable base classifier on Euclidean space. For every $\sigma \in \mathbb{R}$, input $x \in \mathbb{R}^\iota$ and class $c \in Y$, the smoothed class probability

$$p_c(x) = \Pr_{Z \sim \mathcal{N}(0, I)}\big[f(x + \sigma Z) = c\big]$$

equals the probability of the class region $f^{-1}(\{c\})$ under the multivariate Gaussian $\mathcal{N}(x, \sigma^2 I)$:

$$p_c(x) = \mathcal{N}(x, \sigma^2 I)\big(f^{-1}(\{c\})\big).$$
