# Kernel expansion map centered at the sample points

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $V$ be a Hilbert space over $\mathbb{K}$ and let $H$ be a reproducing kernel Hilbert space of functions $X \to V$, with kernel functions $k_x : V \to H$ (the adjoint of evaluation at $x$, so that $\langle f, k_x v \rangle = \langle f(x), v \rangle$). For sample points $x_1, \dots, x_n \in X$, the kernel expansion map is the bounded linear map $V^n \to H$,

$$
c \mapsto \sum_{i=1}^{n} k_{x_i} c_i.
$$

Its range is the span of the kernel functions at the sample points.
