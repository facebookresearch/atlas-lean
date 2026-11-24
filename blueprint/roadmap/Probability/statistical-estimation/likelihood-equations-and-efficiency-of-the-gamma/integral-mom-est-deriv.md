# The expected moment derivative is the moment Jacobian

Let $\mu_X$ be a probability measure on $\mathbb{N}$, the law of a count $K$, and write $E$ for
expectations under $\mu_X$. Let $a, b > 0$, let $\sigma$ be real, let $E K^2 < \infty$, and let $K$
have the negative binomial mean and second moment at $(a, b)$: $E K = m$ and
$E K^2 = m + m^2 / a + m^2$, with $m = \sigma a / b$. Then the expected
[derivative matrix](mom-est-deriv.md) of the moment estimating function at $(a, b)$ is the
[moment Jacobian](mom-jacobian.md): $E\bigl[D_\sigma((a, b), K)\bigr] = J(a, b, \sigma)$.
