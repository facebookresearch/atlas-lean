# Positive tables give every configuration positive probability

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. If every entry of every table is strictly positive, then every configuration $x \in \alpha^n$ has positive joint probability:

$$0 < P(x) .$$
