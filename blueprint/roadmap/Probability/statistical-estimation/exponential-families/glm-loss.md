# Loss of a canonical generalized linear model

Let $\iota$ be a finite index set, $A : \mathbb{R} \to \mathbb{R}$ a function, and $(X_k, Y_k)_{k < m}$ data with features $X_k \in \mathbb{R}^\iota$ and responses $Y_k \in \mathbb{R}$. The loss of the canonical generalized linear model with cumulant function $A$ at $\theta \in \mathbb{R}^\iota$ is

$$\ell(\theta) = \sum_{k < m} \bigl(A(\theta \cdot X_k) - Y_k\, \theta \cdot X_k\bigr).$$

When $A$ is the log-partition function of a one-parameter exponential family and the responses lie in its support, $\ell$ is the negative log-likelihood up to terms that do not depend on $\theta$.
