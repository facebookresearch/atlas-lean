# Asymptotic normality of the method-of-moments estimator

Let $P$ be a probability measure on $\Omega$ and let the counts
$X_0, X_1, \dots : \Omega \to \mathbb{N}$ be mutually independent under $P$, each with law $\mu_X$
on $\mathbb{N}$, the law of a count $K$; write $E$ for expectations under $\mu_X$. Let
$\sigma, a, b > 0$, let $E K^4 < \infty$, and let $K$ have the negative binomial mean and second
moment at $(a, b)$: $E K = m$ and $E K^2 = m + m^2 / a + m^2$, with $m = \sigma a / b$. Let $Y$ be a
random vector in $\mathbb{R}^2$, almost everywhere measurable on a probability space, with
$\langle Y, t \rangle \sim N\bigl(0, E \langle g_\sigma((a, b), K), t \rangle^2\bigr)$ for every
$t \in \mathbb{R}^2$, where $g_\sigma$ is the [moment estimating function](mom-est-fun.md). Then the
[moment estimates](mom-estimator.md) $\hat\theta^{\mathrm{mom}}_n$ satisfy

$$
\sqrt n\, \bigl(\hat\theta^{\mathrm{mom}}_n - (a, b)\bigr) \to -J^{-1} Y
\quad \text{in distribution,}
$$

with $J = J(a, b, \sigma)$ the invertible [moment Jacobian](mom-jacobian.md). No root or consistency
hypothesis is needed: the moment estimate [solves](sum-mom-est-fun-mom-eq-zero.md) the moment
equations once the sample is overdispersed, which happens with probability tending to one, and it is
strongly consistent by the strong law of large numbers (van der Vaart 1998, §4.1 and Theorem 5.41).
