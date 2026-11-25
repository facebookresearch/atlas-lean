# Ratio of weighted proposal sums is the posterior mean

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes, the likelihood weight of an assignment $x$ is $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$, and the proposal $q$ is the joint of the evidence-clamped network, in which every evidence node $k \in E$ has no parents and the point mass at $e_k$ as its table.

For every $f : \alpha^n \to \mathbb{R}$,

$$\frac{\sum_x q(x)\, w_E(x)\, f(x)}{\sum_x q(x)\, w_E(x)} = \mathbb{E}[f \mid X_E = e_E],$$

where the posterior mean uses the convention $t/0 = 0$; both sides are $0$ when the evidence has probability $0$.
