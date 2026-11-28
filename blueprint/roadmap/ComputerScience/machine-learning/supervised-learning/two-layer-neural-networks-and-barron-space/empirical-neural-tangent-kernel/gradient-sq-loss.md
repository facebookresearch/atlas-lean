# Gradient of the square loss

Let $F : \mathbb{R}^P \to \mathbb{R}^n$ be a continuously differentiable map between Euclidean spaces, $y \in \mathbb{R}^n$ fixed targets and $L_y(\theta) = \tfrac12 \sum_i (F(\theta)_i - y_i)^2$ the square loss. Then for every $\theta \in \mathbb{R}^P$ the gradient of $L_y$ is the transposed Jacobian applied to the residual:

$$\nabla L_y(\theta) = J_F(\theta)^{\mathsf T}\,\big(F(\theta) - y\big),$$

where $J_F(\theta)$ is the $n \times P$ Jacobian matrix of $F$ at $\theta$.
