# Argmax invariance

Let $A$ be an $r \times m$ contrast matrix with $A A^\top$ invertible, let $V(\theta)$ be a positive definite $m \times m$ covariance matrix for every parameter $\theta$, let $Q$ be an invertible $r \times r$ matrix, and let $y \in \mathbb R^m$. Let $\ell_A(\theta)$, the restricted log-likelihood, be the log of the $N(0, A V(\theta) A^\top)$ density at $A y$. Then for every parameter set $s$ and every $\theta_0$, $\theta_0$ maximizes $\ell_{QA}$ on $s$ if and only if it maximizes $\ell_A$ on $s$.
