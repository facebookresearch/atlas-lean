# Measurable Bayes actions over a finite action space

Let $\Theta$ be a nonempty standard Borel space, $\mathcal{X}$ a measurable space and $\mathcal{Y}$ a finite nonempty action space with any measurable structure. Let $\ell : \Theta \times \mathcal{Y} \to [0, \infty]$ be a loss such that $\theta \mapsto \ell(\theta, y)$ is measurable for every $y \in \mathcal{Y}$, let $P$ be a finite kernel from $\Theta$ to $\mathcal{X}$ and $\pi$ a finite measure on $\Theta$. Then there is a measurable $f : \mathcal{X} \to \mathcal{Y}$ that minimizes the posterior expected loss almost surely: for almost every $x$ under the marginal $P \circ \pi$,

$$\int \ell(\theta, f(x)) \, d\pi(\theta \mid x) = \inf_{y \in \mathcal{Y}} \int \ell(\theta, y) \, d\pi(\theta \mid x),$$

where $\pi(\cdot \mid x)$ is the posterior on $\Theta$ given $x$.
