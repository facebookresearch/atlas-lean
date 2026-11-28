# Within-class scatter matrix

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, a prior on classes, class means, and a shared precision matrix $S$. Let $(y_k, x_k)_{k < m}$ be labelled data. The pooled scatter matrix of the residuals about class means $\mu$ is $\frac{1}{m} \sum_k (x_k - \mu_{y_k})(x_k - \mu_{y_k})^{\mathsf{T}}$, and the zero matrix when $m = 0$.
