# Fitted values of kernel ridge regression

Let $H$ be a real reproducing kernel Hilbert space of functions $X \to \mathbb{R}$, let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, and let $K$ be the [kernel Gram matrix](kernel-gram.md). For every $j$, the [kernel ridge fit](kernel-ridge-fit.md) $\hat f$ satisfies

$$
\hat f(x_j) = \big(K (K + \lambda I)^{-1} y\big)_j,
$$

where the inverse of a singular matrix is taken to be $0$.
