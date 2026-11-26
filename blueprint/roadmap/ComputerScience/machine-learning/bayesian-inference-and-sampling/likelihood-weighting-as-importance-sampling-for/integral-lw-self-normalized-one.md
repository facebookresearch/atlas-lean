# One-sample self-normalized likelihood weighting

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$ with measurable singletons, conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_k p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a set $E$ of evidence nodes, the likelihood weight of an assignment $x$ is $w_E(x) = \prod_{k \in E} p_k(x_k \mid x_{\mathrm{pa}(k)})$, and the proposal $q$ is the joint of the evidence-clamped network, in which every evidence node $k \in E$ has no parents and the point mass at $e_k$ as its table. Let $\mu$ be a measure on a measurable space $\Omega$ and $X_0, X_1, \ldots : \Omega \to \alpha^n$ measurable samples whose law under $\mu$ is the proposal measure $\sum_x q(x)\,\delta_x$. Then for every $f : \alpha^n \to \mathbb{R}$, the self-normalized estimate from one sample, $w_E(X_0) f(X_0) / w_E(X_0)$ (with $t/0 = 0$), has expectation

$$\sum_{x} q(x) \cdot \begin{cases} 0 & \text{if } w_E(x) = 0, \\ f(x) & \text{otherwise,} \end{cases}$$

the proposal mean of $f$ over assignments of positive weight. This is in general not the posterior mean, so the finite-sample self-normalized estimator is biased.
