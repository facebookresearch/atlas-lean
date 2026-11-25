# Pythagoras for least squares

Let $X$ be a real design matrix with $m$ rows and columns
indexed by a finite type $\iota$, let $y \in \mathbb{R}^m$, write $S$ for the residual sum of
squares, and let $\theta_0 \in \mathbb{R}^\iota$ solve the normal equations
$X^\top X \theta_0 = X^\top y$. Then for every $\theta \in \mathbb{R}^\iota$,

$$S(\theta) = S(\theta_0) + (X(\theta - \theta_0)) \cdot (X(\theta - \theta_0)).$$
