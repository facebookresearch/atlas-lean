# Integrals against the joint measure are finite sums

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$ with measurable singletons, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For every $g : \alpha^n \to \mathbb{R}$, the integral against the joint measure $\mu_B = \sum_x P(x)\,\delta_x$ is

$$\int g \, d\mu_B = \sum_{x \in \alpha^n} P(x)\, g(x) .$$
