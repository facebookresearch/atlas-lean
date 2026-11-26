# Joint distribution of a Bayesian network as a measure

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$ with a measurable structure in which singletons are measurable, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. The joint measure is the finite measure on assignments

$$\mu_B = \sum_{x \in \alpha^n} P(x)\, \delta_x ,$$

the law of one forward sample; it is a probability measure.
