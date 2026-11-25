# Scalar Gaussian channel kernel divergence

Let $N, V > 0$ be noise and reference variances, $m \in \mathbb{R}$ a reference mean, and $\mu$ a probability measure on $\mathbb{R}$ with finite second moment. Let $k$ be the Gaussian noise kernel $x \mapsto \mathcal N(x, N)$. Then

$$\mathrm{KL}\big(\mu \otimes k \,\big\|\, \mu \otimes \mathcal N(m, V)\big) = \left(\frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2\,d\mu(x)}{V} - 1\right)\right)^{+},$$

where $\mu \otimes k$ is the joint law of input and output, $\mu \otimes \mathcal N(m, V)$ is the product measure, and $(\cdot)^+ = \max(\cdot, 0)$ is the embedding of $\mathbb{R}$ into $[0, \infty]$.
