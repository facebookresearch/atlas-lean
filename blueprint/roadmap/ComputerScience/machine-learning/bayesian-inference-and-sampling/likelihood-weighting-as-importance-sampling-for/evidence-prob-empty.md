# Empty evidence has probability one

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For the empty set of evidence nodes and any assignment $e$,

$$P(X_\emptyset = e_\emptyset) = \sum_{x} P(x) = 1 .$$
