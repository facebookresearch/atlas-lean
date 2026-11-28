# Gradient of the GLM loss

Let $A : \mathbb{R} \to \mathbb{R}$ be differentiable with derivative $A'$, and let $(X_k, Y_k)_{k < m}$ be data with $X_k \in \mathbb{R}^\iota$ for a finite index set $\iota$ and $Y_k \in \mathbb{R}$. With $\mathbb{R}^\iota$ carrying the Euclidean inner product, the gradient of the generalized linear model loss at $\theta$ is $\sum_k (A'(\theta \cdot X_k) - Y_k) X_k$.
