# Likelihood in Gaussian discriminant analysis

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, a prior on classes, class means, and a shared precision matrix $S$. Let $(y_k, x_k)_{k < m}$ be labelled data. The likelihood of the data is the product over examples of the joint score $\pi_{y_k}\, g_S(x_k; \mu_{y_k})$, where $g_S(x; \mu)$ is the Gaussian density formula with mean $\mu$ and $S^{-1}$ in place of the covariance. It is the likelihood of the Gaussian model when $S$ is positive definite.
