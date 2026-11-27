# Sheppard's formula (Gaussian arcsine law)

Let $\rho$ be a real number with $-1 < \rho < 1$,
and let $\gamma$ be the multivariate Gaussian measure on $\mathbb{R}^2$ with mean $0$ and
covariance matrix whose diagonal entries are $1$ and whose off-diagonal entries are $\rho$ (the
law of a standard bivariate normal vector with correlation $\rho$). Then the open first quadrant
$\{x \in \mathbb{R}^2 : x_1 > 0,\ x_2 > 0\}$ has $\gamma$-probability
$\frac{1}{4} + \frac{\arcsin \rho}{2\pi}$.

The proof realises $\gamma$ as the law of $(\langle u, r\rangle, \langle v, r\rangle)$ for a standard Gaussian vector
$r$ in the plane and unit vectors $u$, $v$ with $\langle u, v\rangle = \rho$, by comparing characteristic
functions, and then uses the quadrant probability for two directions. That in turn rests on the
random-hyperplane computation of Goemans and Williamson rather than on Sheppard's own argument.
The formula also holds for $\rho = \pm 1$, where the covariance matrix is singular (the quadrant
probability is then $1/2$ or $0$), and the same argument covers it; the statement above assumes $|\rho| < 1$.

## Informally uses

- [Quadrant probability for two directions](std-gaussian-pos-pos.md): the probability in
  terms of the inner product $\rho$ of the two directions.
- [Characteristic function of a pair of inner products](char-fun-map-inner-pair.md): the
  identification of $\gamma$ with the law of $(\langle u, r\rangle, \langle v, r\rangle)$.

## Background

- [Goemans–Williamson Lemma 3.2](../../../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/measure-real-sign-ne.md):
  the same fact in hyperplane form, which is how semidefinite rounding uses it.

## Sources

- Y. L. Tong, The Multivariate Normal Distribution, Springer, 1990, Ch. 3; W. F. Sheppard, "On the application of the theory of error to cases of normal distribution and normal correlation", Phil. Trans. R. Soc. Lond. A 192 (1899), 101–167; https://en.wikipedia.org/wiki/Multivariate_normal_distribution
