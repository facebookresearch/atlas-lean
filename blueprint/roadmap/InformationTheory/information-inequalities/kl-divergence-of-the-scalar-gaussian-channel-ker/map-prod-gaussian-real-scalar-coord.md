# Map prod gaussian Real scalar Coord

Let $\iota : \mathbb{R} \to \mathbb{R}^1$ be the linear isometry onto one-dimensional Euclidean space sending $x$ to the vector $(x)$ whose only coordinate is $x$.

Let $m \in \mathbb{R}$, $V \ge 0$, and let $\mu$ be a probability measure on $\mathbb{R}$. The image of the product measure $\mu \times \mathcal{N}(m, V)$ under $(x, y) \mapsto (\iota(x), \iota(y))$ is the product of $\iota_* \mu$ with the Gaussian on $\mathbb{R}^1$ with mean $\iota(m)$ and $1 \times 1$ covariance matrix $(V)$:

$$(\iota \times \iota)_* \big(\mu \times \mathcal{N}(m, V)\big) = (\iota_* \mu) \times \mathcal{N}\big(\iota(m), (V)\big).$$
