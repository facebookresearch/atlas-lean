# Dirichlet's theorem on pointwise convergence of Fourier series

Let
$f \colon \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and continuously differentiable, and for
$n \in \mathbb{Z}$ let $\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ be the $n$-th
Fourier coefficient of $f$ on $[0, 2\pi]$. Then for every $x \in \mathbb{R}$ the symmetric Fourier
partial sums $S_N(f)(x) = \sum_{n=-N}^{N} \hat f_n e^{inx}$ converge to $f(x)$ as $N \to \infty$.

## Sources

- P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `fourier_dirichlet_fejer` of the lean-eval benchmark.
