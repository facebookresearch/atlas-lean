# The gradient of the log-partition function with base weights is the mean

Let $X$ be a finite set, $\iota$ a finite index set, $h : X \to \mathbb{R}$ base weights and $T : X \to \mathbb{R}^\iota$ a sufficient statistic, with $h(x) \ge 0$ for every $x$ and $\sum_x h(x) > 0$. Then at every
$\eta \in \mathbb{R}^\iota$, with the Euclidean inner product, the log-partition function
$A(\eta) = \log \sum_x h(x) e^{\eta \cdot T(x)}$ has gradient

$$\nabla A(\eta) = \sum_{x \in X} p_\eta(x)\, T(x), \qquad p_\eta(x) = h(x)\, e^{\eta \cdot T(x) - A(\eta)} ,$$

the mean of $T$ under $p_\eta$. This is the form with base weights of
[the gradient of the log-partition function](has-gradient-at-log-partition.md).
