# Kernel ridge regression objective

Let $H$ be a real inner product space of functions $X \to \mathbb{R}$ on which evaluation at each point is continuous (a reproducing kernel space; completeness is not needed for this definition), let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$. The kernel ridge objective of $f \in H$ is

$$
\sum_{i=1}^{n} \big(y_i - f(x_i)\big)^2 + \lambda \|f\|^2.
$$
