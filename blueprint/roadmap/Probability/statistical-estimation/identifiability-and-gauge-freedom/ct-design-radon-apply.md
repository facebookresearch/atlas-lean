# The Radon transform of a finite superposition is the design sum

Let $s$ be a finite index set, $\varphi_i \colon \mathbb{R}^2 \to \mathbb{R}$ functions, $x_i$ real
coefficients, $\xi \in \mathbb{R}^2$ and $p$ real, and suppose every $\varphi_i$ with $i \in s$ is
integrable on the set $\{y : \langle y, \xi \rangle = p\}$ for the one-dimensional Hausdorff
measure. Then the Euclidean Radon transform $R$ of the superposition satisfies

$$R\Big(\sum_{i \in s} x_i \varphi_i\Big)(\xi, p) = \sum_{i \in s} x_i\, a_i(\xi, p),$$

where $a_i(\xi, p) = R\varphi_i(\xi, p)$ is the [design entry](ct-design-entry.md) of $\varphi_i$.
