# Directional derivative of the GLM loss

Let $\iota$ be a finite index set, $A : \mathbb{R} \to \mathbb{R}$ differentiable with derivative $A'$, and $(X_k, Y_k)_{k < m}$ data with $X_k \in \mathbb{R}^\iota$ and $Y_k \in \mathbb{R}$. The loss of the canonical generalized linear model is $\ell(\theta) = \sum_{k < m} \bigl(A(\theta \cdot X_k) - Y_k\, \theta \cdot X_k\bigr)$. Then for all $\theta, v \in \mathbb{R}^\iota$ the function $t \mapsto \ell(\theta + t v)$ is differentiable at $t = 0$ with derivative

$$\frac{d}{dt}\Big|_{t=0} \ell(\theta + t v) = \sum_{k < m} \bigl(A'(\theta \cdot X_k) - Y_k\bigr)\, (v \cdot X_k).$$
