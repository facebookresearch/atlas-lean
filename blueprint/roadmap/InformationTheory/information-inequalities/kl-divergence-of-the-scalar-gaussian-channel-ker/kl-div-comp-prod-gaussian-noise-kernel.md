# Scalar Gaussian channel kernel divergence

Let $m \in \mathbb{R}$, let $N > 0$ and $V > 0$ be noise and reference variances, and let $\mu$ be a probability measure on $\mathbb{R}$ with finite second moment ($\int x^2 \, d\mu < \infty$). Let $k$ be the additive Gaussian noise kernel $k_N(x) = \mathcal{N}(x, N)$, the law of $x + Z$ with $Z \sim \mathcal{N}(0, N)$. Then the Kullback-Leibler divergence, in nats, of the joint law $\mu \otimes k$ from the product $\mu \times \mathcal{N}(m, V)$ is

$$\mathrm{KL}\big(\mu \otimes k \,\|\, \mu \times \mathcal{N}(m, V)\big) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\mu(x)}{V} - 1\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
