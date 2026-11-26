# The gradient of log-sum-exp is the softmax

With $\operatorname{lse}(z) = \log \sum_i e^{z_i}$ and $\operatorname{softmax}(z)_i = e^{z_i} / \sum_j e^{z_j}$ on a nonempty finite index set, log-sum-exp on the Euclidean space $\mathbb{R}^\iota$ has gradient $\operatorname{softmax}(z)$ at every $z$.
