# The rectangular inverse DFT as a two-dimensional exponential sum

Let $m, n \ge 1$ and let $X$ be a complex array on $\mathbb{Z}/m \times \mathbb{Z}/n$. The rectangular inverse discrete Fourier transform of $X$, computed by inverse transforms along columns and then rows, is the two-dimensional positive-exponent sum

$$\check X(i, j) = \frac{1}{mn} \sum_{k \in \mathbb{Z}/m} \sum_{l \in \mathbb{Z}/n} \exp\Big(2\pi i \Big(\frac{\bar k\, \bar i}{m} + \frac{\bar l\, \bar j}{n}\Big)\Big) X(k, l),$$

where $\bar k \in \{0, \dots, m - 1\}$ is the representative of $k$. The sizes must be positive: $\mathbb{Z}/0$ is the integers, not a set of zero points, and $1/(mn)$ is not a normalization there.
