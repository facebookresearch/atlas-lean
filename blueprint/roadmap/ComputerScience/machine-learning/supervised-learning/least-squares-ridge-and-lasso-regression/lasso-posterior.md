# Lasso posterior kernel

Let $X$ be a real matrix with $m$ rows and columns indexed by a
finite set $\iota$, let $y \in \mathbb{R}^m$, and let $v \ge 0$ and $b \ge 0$. The lasso posterior
kernel at $\theta \in \mathbb{R}^\iota$ is

$$\prod_{k=1}^{m} \varphi_v\bigl(y_k - (X\theta)_k\bigr) \cdot \prod_{i \in \iota} p_b(\theta_i),$$

where $\varphi_v(x) = e^{-x^2/(2v)} / \sqrt{2\pi v}$ is the density of the normal distribution with
mean $0$ and variance $v$ and $p_b(x) = e^{-|x|/b} / (2b)$ is the density of the Laplace
distribution with location $0$ and scale $b$: the Gaussian likelihood of $y$ with noise variance
$v$ times the Laplace prior density of $\theta$.

It is a meaningful kernel for $v \ne 0$ and $b \ne 0$; for $v = 0$ (respectively $b = 0$) the
normal (respectively Laplace) density is the zero function.
