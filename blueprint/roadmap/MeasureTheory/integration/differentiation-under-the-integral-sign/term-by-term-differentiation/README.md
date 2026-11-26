# Differentiating an integral of a series term by term

Let $\Omega \subseteq \mathbb{R}^d$ be open, let $a < c < b$, and let
$f_n : \mathbb{R}^d \times \mathbb{R} \to \mathbb{C}$, $n \in \mathbb{N}$, be almost everywhere
measurable on $\Omega \times (a, b)$. Write $\partial_y f_n$ for the derivative in the second
variable, taken to be $0$ where it does not exist, and give every series that does not converge
absolutely the sum $0$. Suppose that for each $n$ and almost every $x \in \Omega$ the function
$y \mapsto f_n(x, y)$ is absolutely continuous on $[a, b]$; that each $\partial_y f_n$ is almost
everywhere measurable on $\Omega \times (a, b)$, the series $\sum_n |\partial_y f_n(x, y)|$
converges for almost every $(x, y) \in \Omega \times (a, b)$, and its sum is integrable on
$\Omega \times (a, b)$; and that the series $\sum_n |f_n(x, c)|$ converges for almost every
$x \in \Omega$ and its sum is integrable on $\Omega$. Then there is a function $F : \mathbb{R} \to \mathbb{C}$
such that, for almost every $y \in (a, b)$, the function $x \mapsto \sum_n f_n(x, y)$ is integrable
on $\Omega$, $F(y) = \int_\Omega \sum_n f_n(x, y)\, dx$, and $F$ is differentiable at $y$ with
$F'(y) = \sum_n \int_\Omega \partial_y f_n(x, y)\, dx$.

## Idea

Absolute continuity recovers each term from its derivative:
$f_n(x, y) = f_n(x, c) + \int_c^y \partial_y f_n(x, t)\, dt$. The two integrable bounds let Fubini's
theorem exchange the sum over $n$, the integral over $\Omega$ and the integral in $t$, so that
$F(y) = F(c) + \int_c^y G(t)\, dt$ with $G(t) = \sum_n \int_\Omega \partial_y f_n(x, t)\, dx$
integrable. Lebesgue's differentiation theorem then gives $F'(y) = G(y)$ for almost every $y$. The
joint measurability of the $f_n$ cannot be dropped; the statement page gives an example.

## Statements

- [Differentiating an integral of a series term by term](exists-has-deriv-at-integral-tsum-ae.md)
