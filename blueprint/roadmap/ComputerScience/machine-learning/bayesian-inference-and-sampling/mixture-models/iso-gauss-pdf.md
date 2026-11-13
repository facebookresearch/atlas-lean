# Isotropic Gaussian density

For a mean $\mu \in \mathbb{R}^d$ and a variance $v \ge 0$,
the isotropic Gaussian density at $x \in \mathbb{R}^d$ is
$\mathcal{N}(x \mid \mu, v I) = \prod_{i=1}^{d} \varphi_{\mu_i, v}(x_i)$, where
$\varphi_{m, v}$ is the one-dimensional Gaussian density with mean $m$ and variance $v$.

For $v = 0$ the one-dimensional density is identically $0$, following Mathlib's convention.
