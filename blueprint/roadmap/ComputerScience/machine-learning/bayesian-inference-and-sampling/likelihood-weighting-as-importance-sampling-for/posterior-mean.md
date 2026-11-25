# Posterior mean in a Bayesian network

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes, an evidence assignment $e$ and a function $f : \alpha^n \to \mathbb{R}$, the posterior mean is

$$\mathbb{E}[f \mid X_E = e_E] = \frac{\sum_{x \,:\, x_k = e_k\ \forall k \in E} P(x)\, f(x)}{P(X_E = e_E)},$$

with the convention $t / 0 = 0$, so it is $0$ when the evidence has probability $0$.
