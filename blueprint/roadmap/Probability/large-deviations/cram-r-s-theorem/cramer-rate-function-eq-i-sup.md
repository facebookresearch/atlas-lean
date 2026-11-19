# Cramér rate function as a supremum

Let $\mu$ be a measure on $\Omega$, $X : \Omega \to \mathbb{R}^d$ and $x \in \mathbb{R}^d$, and let
$\bar\Lambda$ be the [extended log moment generating function](extended-log-mgfvec.md). Then the
[Cramér rate function](cramer-rate-function.md) is

$$I(x) = \sup_{t \in \mathbb{R}^d} \big(\langle t, x\rangle - \bar\Lambda(t)\big)^+ \in [0, \infty],$$

where $(\cdot)^+$ sends a value of $[-\infty, \infty]$ to $[0, \infty]$, negative values going to
$0$.
