# Probability of evidence in a Bayesian network

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes and an evidence assignment $e$, the probability of the evidence is

$$P(X_E = e_E) = \sum_{x \,:\, x_k = e_k \ \forall k \in E} P(x) \in \mathbb{R}.$$
