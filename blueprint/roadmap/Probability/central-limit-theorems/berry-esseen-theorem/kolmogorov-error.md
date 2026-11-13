# Kolmogorov error

For a measure $\mu$ on $\mathbb{R}$ and a positive integer $n$, the
Kolmogorov error of $\mu$ at $n$ is the real supremum
$\sup_{x \in \mathbb{R}} |F_{\mu,n}(x) - \Phi(x)|$, where $\Phi$ is the standard normal
cumulative distribution function and $F_{\mu,n}$ is Mathlib's cumulative distribution function
of the normalized law of $\mu$ at $n$. When $\mu$ is a probability measure, $F_{\mu,n}(x)$ is
the mass the normalized law gives to $(-\infty, x]$; otherwise the normalized law is the zero
measure and $F_{\mu,n}$ is a fixed but unspecified cumulative distribution function of some
probability measure, not the zero function.

The values $|F_{\mu,n}(x) - \Phi(x)|$ lie in $[0, 1]$, so the supremum is finite.
