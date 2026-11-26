# Map comp Prod noise Kernel scalar Coord

Let $\iota : \mathbb{R} \to \mathbb{R}^1$ be the linear isometry onto one-dimensional Euclidean space sending $x$ to the vector $(x)$ whose only coordinate is $x$.

Let $N \ge 0$ and let $\mu$ be a probability measure on $\mathbb{R}$. Let $k$ be the kernel $x \mapsto \mathcal{N}(x, N)$ on $\mathbb{R}$, and let $K$ be the kernel on $\mathbb{R}^1$ sending $y$ to the law of $H y + Z$, where $H = (1)$ is the $1 \times 1$ identity matrix and $Z$ has the one-dimensional Gaussian law with mean $0$ and covariance matrix $(N)$. Then the image of the joint law $\mu \otimes k$ under $(x, y) \mapsto (\iota(x), \iota(y))$ is the joint law of the image input law with $K$:

$$(\iota \times \iota)_* (\mu \otimes k) = (\iota_* \mu) \otimes K.$$
