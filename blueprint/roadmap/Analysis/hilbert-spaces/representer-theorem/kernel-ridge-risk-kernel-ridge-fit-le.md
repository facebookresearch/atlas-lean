# Kernel ridge regression

Let $H$ be a real reproducing kernel Hilbert space of functions $X \to \mathbb{R}$, let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$ and $\lambda > 0$. The [kernel ridge fit](kernel-ridge-fit.md) minimizes the [kernel ridge objective](kernel-ridge-risk.md) $\sum_i (y_i - f(x_i))^2 + \lambda \|f\|^2$ over the whole space $H$. This is the result of G. S. Kimeldorf and G. Wahba, *Some results on Tchebycheffian spline functions*, J. Math. Anal. Appl. 33 (1971).
