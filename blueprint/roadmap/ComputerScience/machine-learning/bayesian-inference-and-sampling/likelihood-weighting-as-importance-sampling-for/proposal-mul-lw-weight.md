# Proposal times likelihood weight is the joint restricted to the evidence

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes, the likelihood weight of an assignment $x$ is $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$, and the proposal $q$ is the joint of the evidence-clamped network, in which every evidence node $k \in E$ has no parents and the point mass at $e_k$ as its table.

Then for every assignment $x$,

$$q(x)\, w_E(x) = \begin{cases} P(x) & \text{if } x_k = e_k \text{ for all } k \in E, \\ 0 & \text{otherwise.} \end{cases}$$
