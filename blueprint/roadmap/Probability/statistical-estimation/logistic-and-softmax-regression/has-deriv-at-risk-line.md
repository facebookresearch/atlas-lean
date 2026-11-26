# Directional derivative of the empirical logistic risk

Let $\iota$ be a finite index set and $(X_k, Y_k)_{k < m}$ data with features $X_k \in \mathbb{R}^\iota$ and Boolean labels $Y_k$, written $y_k \in \{0, 1\}$. The empirical logistic risk is $R(w) = \sum_{k < m} \bigl(\log(1 + e^{w \cdot X_k}) - y_k\, w \cdot X_k\bigr)$. For all $w, v \in \mathbb{R}^\iota$ the function $t \mapsto R(w + t v)$ is differentiable at $t = 0$ with derivative

$$\frac{d}{dt}\Big|_{t=0} R(w + t v) = \sum_{k < m} \bigl(\sigma(w \cdot X_k) - y_k\bigr)\, (v \cdot X_k),$$

where $\sigma(z) = 1 / (1 + e^{-z})$ is the logistic function.
