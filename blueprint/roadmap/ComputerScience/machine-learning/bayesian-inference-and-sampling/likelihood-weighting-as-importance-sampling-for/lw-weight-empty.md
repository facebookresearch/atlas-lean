# Likelihood weight without evidence is one

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For the empty set of evidence nodes, the likelihood weight $w_\emptyset(x) = \prod_{k \in \emptyset} p_k(x_k \mid x_{\mathrm{pa}(k)})$ of every assignment $x$ equals $1$.
