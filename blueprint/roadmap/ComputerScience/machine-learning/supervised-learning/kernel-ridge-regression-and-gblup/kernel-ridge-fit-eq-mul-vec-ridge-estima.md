# Kernel ridge regression = GBLUP = RR-BLUP

Let $H$ be a real reproducing kernel Hilbert space of functions on a set $X$, let $x_1, \dots, x_m \in X$ be training inputs whose kernel Gram matrix is $Z Z^\top$ for a matrix $Z \in \mathbb{R}^{m \times \iota}$ with $\iota$ finite, let $y \in \mathbb{R}^m$ and $\lambda > 0$. Then the kernel ridge fit, the minimizer of $\sum_i (y_i - f(x_i))^2 + \lambda \|f\|_H^2$ over $f \in H$, has fitted values $f(x_j) = (Z \hat\beta)_j$ for every $j$, where $\hat\beta = (Z^\top Z + \lambda I)^{-1} Z^\top y$ are the ridge marker effects.
