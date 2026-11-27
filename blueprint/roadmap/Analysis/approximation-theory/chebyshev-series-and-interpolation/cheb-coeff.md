# Chebyshev coefficients

For $f : \mathbb{R} \to \mathbb{C}$ (only its values on $[-1, 1]$ matter),
$a_k = \frac{2}{\pi} \int_0^\pi f(\cos\theta)\cos(k\theta) \, d\theta$ for $k \ge 1$ and
$a_0 = \frac{1}{\pi} \int_0^\pi f(\cos\theta)\, d\theta$, each integral taken to be $0$ when its
integrand is not integrable on $[0, \pi]$. When $\theta \mapsto f(\cos\theta)$ is integrable, the
substitution $x = \cos\theta$ turns these into
$\frac{2}{\pi}\int_{-1}^1 f(x) T_k(x) (1 - x^2)^{-1/2} dx$ (and $\frac1\pi$ for $k = 0$).

## Sources

- L. N. Trefethen, Approximation Theory and Approximation Practice, SIAM (2013; extended edition 2019), Chapter 3.
