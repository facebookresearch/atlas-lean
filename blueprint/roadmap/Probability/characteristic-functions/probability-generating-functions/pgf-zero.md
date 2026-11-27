# The generating function at $s = 0$

Let $\mu$ be a measure on $\Omega$ and let
$X : \Omega \to \mathbb{N}$ be measurable. Then the probability generating function
$G_X(s) = \int_\Omega s^{X(\omega)} \, d\mu(\omega)$ of $X$ under $\mu$ satisfies
$G_X(0) = \mu(\lbrace \omega : X(\omega) = 0 \rbrace)$, where the measure of the event is read as
a real number, an infinite value being read as $0$.

When $\mu$ is a probability measure this is the probability that $X = 0$, and when $\mu$ is finite
it is the mass of that event.
