# Cramér rate function agrees with the extended conjugate

Let $\mu$ be a probability measure on $\Omega$, let $X : \Omega \to \mathbb{R}^d$ and
$x \in \mathbb{R}^d$. Then the [Cramér rate function](cramer-rate-function.md) $I(x) \in [0, \infty]$,
viewed in $[-\infty, \infty]$, equals the Legendre transform of the [extended log moment
generating function](extended-log-mgfvec.md) $\bar\Lambda$:

$$I(x) = \bar\Lambda^*(x) = \sup_{t \in \mathbb{R}^d} \big(\langle t, x\rangle - \bar\Lambda(t)\big).$$

Under a probability measure this supremum is nonnegative, so no value is lost in passing to
$[0, \infty]$.
