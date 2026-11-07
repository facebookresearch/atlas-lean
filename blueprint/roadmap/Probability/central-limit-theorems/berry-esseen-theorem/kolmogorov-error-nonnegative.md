# The Kolmogorov error is nonnegative

For every measure $\mu$ on $\mathbb{R}$ and every
positive integer $n$, the Kolmogorov error of $\mu$ at $n$, that is
$\sup_{x \in \mathbb{R}} |F_{\mu,n}(x) - \Phi(x)|$ where $F_{\mu,n}$ is Mathlib's cumulative
distribution function of the normalized law of $\mu$ at $n$ and $\Phi$ is the standard normal
cumulative distribution function, is nonnegative.

Here $F_{\mu,n}(x)$ is the mass the normalized law gives to $(-\infty, x]$ when $\mu$ is a
probability measure; otherwise the normalized law is the zero measure and $F_{\mu,n}$ is a
fixed but unspecified cumulative distribution function of some probability measure.
