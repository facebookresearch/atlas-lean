# The log marginal likelihood of Gaussian-process regression

Let $k : X \times X \to \mathbb{R}$ be a kernel and $x = (x_j)_{j \in \nu}$ a finite family of $n = |\nu|$ training inputs whose kernel matrix $K = K(x, x)$ is positive semidefinite, and let $\sigma^2 > 0$. Then for every $y \in \mathbb{R}^\nu$ the logarithm of the Gaussian density $\mathcal{N}(y \mid 0, K + \sigma^2 I)$ at the targets $y$ is the [log marginal likelihood](log-marginal-likelihood.md)

$$-\tfrac12\, y^\top (K + \sigma^2 I)^{-1} y - \tfrac12 \log \det(K + \sigma^2 I) - \tfrac{n}{2} \log 2\pi$$

(Rasmussen and Williams 2006, Equation 2.30). Together with the marginal law of the targets, this says that the log marginal likelihood is the logarithm of the density of $y$ after the latent function values have been integrated out.
