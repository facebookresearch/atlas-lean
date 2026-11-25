# Regularized risk in a reproducing kernel Hilbert space

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $V$ be an inner product space over $\mathbb{K}$ and let $H$ be an inner product space over $\mathbb{K}$ of functions $X \to V$ on which evaluation at each point is continuous (a reproducing kernel space; completeness of $H$ and $V$ is not needed for this definition). For sample points $x_1, \dots, x_n \in X$, a loss $L : V^n \to \mathbb{R}$ and a regularizer $\Omega : \mathbb{R} \to \mathbb{R}$, the regularized risk of $f \in H$ is

$$
L\big(f(x_1), \dots, f(x_n)\big) + \Omega(\|f\|).
$$
