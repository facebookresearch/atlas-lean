# Empirical Process

Let $\mu$ be a measure on a measurable space $S$, let $X_0, X_1, \dots : \Omega \to S$ be a sequence of maps, $n \in \mathbb{N}$ and $f : S \to \mathbb{R}$. The empirical process at $f$ is

$$\mathbb{G}_n f(\omega) = \frac{1}{\sqrt{n}} \sum_{k=0}^{n-1} \Big( f(X_k(\omega)) - \int_S f \, d\mu \Big),$$

with the conventions $1/\sqrt{0} = 0$, so $\mathbb{G}_0 f = 0$, and $\int_S f \, d\mu = 0$ when $f$ is not $\mu$-integrable.
