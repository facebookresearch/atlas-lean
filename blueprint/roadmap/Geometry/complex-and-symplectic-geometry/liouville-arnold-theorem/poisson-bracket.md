# Standard Poisson bracket on $\mathbb{R}^{2n}$

Write the coordinates of a point
$x \in \mathbb{R}^{2n}$ as $p_i = x_i$ and $q_i = x_{n+i}$ for $i = 0, \dots, n-1$. For functions
$F, G \colon \mathbb{R}^{2n} \to \mathbb{R}$, the Poisson bracket for the symplectic form
$\omega_0 = \sum_i dp_i \wedge dq_i$ is the function

$$
\{F, G\}(x) = \sum_{i=0}^{n-1} \left( \frac{\partial F}{\partial p_i}(x)
\frac{\partial G}{\partial q_i}(x) - \frac{\partial F}{\partial q_i}(x)
\frac{\partial G}{\partial p_i}(x) \right).
$$

Partial derivatives are read off the Fréchet derivative, which is taken to be zero at points
where the function is not differentiable.
