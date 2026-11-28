# Observed information

For a parametric family of densities $p_\theta$, $\theta$ in a finite-dimensional real inner product space $E$, with score $s_\theta(x) = \nabla_\theta\log p_\theta(x)$, a sample $x_0, x_1, \dots$ and $n \in \mathbb{N}$, the observed information at $\theta$ is the operator

$$\hat J_n(\theta) = -\frac1n\sum_{i<n}D_\theta s_\theta(x_i),$$

minus the average derivative of the score (minus the average Hessian of the log-likelihood); it is $0$ for $n = 0$.
