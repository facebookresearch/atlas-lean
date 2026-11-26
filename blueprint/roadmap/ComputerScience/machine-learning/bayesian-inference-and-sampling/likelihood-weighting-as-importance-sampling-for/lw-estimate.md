# Likelihood-weighting estimate

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. Let $E$ be a set of evidence nodes, $f : \alpha^n \to \mathbb{R}$, and $X_0, X_1, \ldots : \Omega \to \alpha^n$ samples. The likelihood-weighting estimate from the first $m$ samples at $\omega \in \Omega$ is the importance-sampling average with the likelihood weight $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$:

$$\widehat{L}_m(\omega) = \frac{1}{m} \sum_{i < m} w_E(X_i(\omega))\, f(X_i(\omega)),$$

which is $0$ when $m = 0$.
