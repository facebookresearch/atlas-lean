# Positive tables give every evidence positive probability

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a finite nonempty type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. If every entry of every table is strictly positive, then for every set $E$ of evidence nodes and every evidence assignment $e$,

$$P(X_E = e_E) = \sum_{x \,:\, x_k = e_k \ \forall k \in E} P(x) \ne 0 .$$
