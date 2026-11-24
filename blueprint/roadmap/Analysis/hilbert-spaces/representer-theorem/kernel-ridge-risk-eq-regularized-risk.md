# Kernel ridge objective as a regularized risk

Let $H$ be a real inner product space of functions $X \to \mathbb{R}$ on which evaluation at each point is continuous (a reproducing kernel space; completeness is not needed here), let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$. For every $f \in H$, the [kernel ridge objective](kernel-ridge-risk.md) equals the [regularized risk](regularized-risk.md) with the squared loss $L(v) = \sum_i (y_i - v_i)^2$ and the regularizer $\Omega(t) = \lambda t^2$.
