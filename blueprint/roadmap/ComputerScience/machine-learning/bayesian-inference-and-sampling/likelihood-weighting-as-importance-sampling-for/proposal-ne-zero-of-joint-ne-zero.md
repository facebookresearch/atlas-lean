# Likelihood-weighting proposal covers the target

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes, the likelihood weight of an assignment $x$ is $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$, and the proposal $q$ is the joint of the evidence-clamped network, in which every evidence node $k \in E$ has no parents and the point mass at $e_k$ as its table.

If an assignment $x$ agrees with the evidence ($x_k = e_k$ for all $k \in E$) and $P(x) \ne 0$, then

$$q(x) \ne 0 \quad\text{and}\quad w_E(x) \ne 0 .$$

So likelihood weighting never meets the zero-proposal-support failure of importance sampling.
