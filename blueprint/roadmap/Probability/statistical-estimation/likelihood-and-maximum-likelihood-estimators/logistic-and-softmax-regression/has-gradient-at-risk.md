# Gradient of the empirical logistic risk

For data $(X_k, Y_k)_{k < m}$ with features $X_k \in \mathbb{R}^\iota$, for a finite index set $\iota$, and Boolean labels $Y_k$, the empirical logistic risk is differentiable at every weight vector, and with $\mathbb{R}^\iota$ carrying the Euclidean inner product its gradient at $w$ is $\sum_{k<m} (\sigma(w \cdot X_k) - y_k) X_k$, where $y_k \in \{0, 1\}$ is the label as a number and $\sigma(z) = 1/(1 + e^{-z})$ is the logistic function.
