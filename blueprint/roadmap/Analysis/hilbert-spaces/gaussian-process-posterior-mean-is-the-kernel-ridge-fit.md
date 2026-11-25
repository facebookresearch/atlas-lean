# Gaussian-process posterior mean is the kernel ridge fit

Let $k$ be the reproducing kernel of a real reproducing kernel Hilbert space $H$ of functions $X \to \mathbb{R}$, let $x_1, \dots, x_n \in X$, $y \in \mathbb{R}^n$,
$\sigma^2 > 0$, and let $K$ be the kernel Gram matrix. For a zero-mean Gaussian process prior with covariance function $k$ and observations
$y_i = f(x_i) + \varepsilon_i$ with $\varepsilon_1, \dots, \varepsilon_n$ independent $\mathcal{N}(0, \sigma^2)$ and independent of $f$, the posterior mean is
$\bar f(x) = \sum_{i=1}^n c_i\, k(x_i, x)$ with $c = (K + \sigma^2 I)^{-1} y$. This is the kernel ridge fit with regularization parameter $\lambda = \sigma^2$, so the
posterior mean is the unique minimizer over $H$ of $\sum_{i=1}^n (y_i - g(x_i))^2 + \sigma^2 \lVert g \rVert_H^2$.

## Expansion

This page becomes ready once this prerequisite is stated:

- Proof prerequisite: the posterior mean of Gaussian-process regression with independent Gaussian noise, $\bar f(x) = k_x^{\mathsf T}(K + \sigma^2 I)^{-1} y$ with $k_x = (k(x_i, x))_i$, from conditioning of jointly Gaussian vectors (statement prerequisite; not yet stated)

## Depends on

- [Kernel ridge regression fit](representer-theorem/kernel-ridge-fit.md)

## Proof depends on

- [Kernel ridge regression](representer-theorem/kernel-ridge-risk-kernel-ridge-fit-le.md)
- [Kernel ridge fit is the unique minimizer](representer-theorem/eq-kernel-ridge-fit-of-le.md)

## Sources

- C. E. Rasmussen and C. K. I. Williams, *Gaussian Processes for Machine Learning*, MIT Press, 2006, Section 2.2: the posterior mean $\bar f_* = k_*^{\mathsf T}(K + \sigma_n^2 I)^{-1}y$, Eq. (2.25), and its kernel expansion $\sum_i \alpha_i k(x_i, x_*)$ with $\alpha = (K + \sigma_n^2 I)^{-1}y$, Eq. (2.27). <http://gaussianprocess.org/gpml/chapters/RW2.pdf>
