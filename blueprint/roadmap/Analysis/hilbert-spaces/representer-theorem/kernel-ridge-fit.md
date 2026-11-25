# Kernel ridge regression fit

Let $H$ be a real reproducing kernel Hilbert space of functions $X \to \mathbb{R}$ with kernel functions $k_x$, let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, and let $K$ be the [kernel Gram matrix](kernel-gram.md). The kernel ridge fit is the [kernel expansion](kernel-expansion.md) $\sum_{i=1}^n c_i k_{x_i}$ with coefficients $c = (K + \lambda I)^{-1} y$, where the inverse of a singular matrix is taken to be $0$.
