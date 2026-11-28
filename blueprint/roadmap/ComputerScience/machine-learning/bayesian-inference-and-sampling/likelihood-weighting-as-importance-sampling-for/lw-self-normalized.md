# Self-normalized likelihood-weighting estimate

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. Let $E$ be a set of evidence nodes, $f : \alpha^n \to \mathbb{R}$ and $X_0, X_1, \ldots : \Omega \to \alpha^n$ samples, with likelihood weight $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$. The self-normalized estimate from the first $m$ samples is the ratio of the likelihood-weighting estimates of $f$ and of the constant $1$:

$$\frac{\frac{1}{m}\sum_{i<m} w_E(X_i)\, f(X_i)}{\frac{1}{m}\sum_{i<m} w_E(X_i)} ,$$

with the convention $t / 0 = 0$.
