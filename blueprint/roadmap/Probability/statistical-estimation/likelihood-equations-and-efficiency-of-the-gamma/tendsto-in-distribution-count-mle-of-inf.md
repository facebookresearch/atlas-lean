# Asymptotic normality of consistent score roots, information form

Let $P$ be a probability measure on $\Omega$ and let the counts
$X_0, X_1, \dots : \Omega \to \mathbb{N}$ be mutually independent under $P$, each with law $\mu_X$
on $\mathbb{N}$, the law of a count $K$; write $E$ for expectations under $\mu_X$. Let $\sigma > 0$
and $\theta_0 = (a, b)$ with $a, b > 0$, and let $E K^2 < \infty$. Assume the score equations at the
truth, $E[\psi_\sigma(\theta_0, K)] = 0$ for the [score of one count](count-score.md)
$\psi_\sigma(\theta, k)$ (the rate coordinate then
[forces](integral-nat-cast-of-integral-count-scor.md) $E K = \sigma a / b$), and the
profile-information condition $\tau_0 > \sigma / (a (b + \sigma))$ for $\tau_0 = E[\varphi_K(a)]$,
the expected [trigamma increment](trigamma-increment.md), which makes the
[Fisher information matrix](count-fisher-info.md) $I = I(a, b, \sigma, \tau_0)$ invertible. Let
$\hat\theta_n : \Omega \to \mathbb{R}^2$ be almost everywhere measurable estimates that are roots of
the joint score equations with probability tending to one,
$P\bigl(\sum_{i < n} \psi_\sigma(\hat\theta_n, X_i) \ne 0\bigr) \to 0$, and consistent,
$\hat\theta_n \to \theta_0$ in $P$-probability. By the [summed scores](sum-count-score.md) the joint
score equations are the shape and rate score equations of the first $n$ counts. Assume moreover the
information identity $E \langle \psi_\sigma(\theta_0, K), t \rangle^2 = \langle I t, t \rangle$ for
every $t \in \mathbb{R}^2$, and let $Y$ be a random vector in $\mathbb{R}^2$, almost everywhere
measurable on a probability space, with $\langle Y, t \rangle \sim N(0, \langle I t, t \rangle)$ for
every $t$. Then $\sqrt n\, (\hat\theta_n - \theta_0) \to I^{-1} Y$ in distribution, and the
[projections of the limit](has-law-inner-inverse-count-fisher-info.md) are
$\langle I^{-1} Y, u \rangle \sim N(0, \langle I^{-1} u, u \rangle)$: the limit is $N(0, I^{-1})$.
