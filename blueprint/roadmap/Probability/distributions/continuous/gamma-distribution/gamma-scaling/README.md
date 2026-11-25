# Scaling a gamma random variable

Let $a, r, c > 0$. The image of the gamma law $\Gamma(a, r)$ with shape $a$ and rate $r$ under
$x \mapsto cx$ is $\Gamma(a, r/c)$: if $X \sim \Gamma(a, r)$ then $cX \sim \Gamma(a, r/c)$.

## Idea

The rate is an inverse scale parameter: multiplying a gamma variable by $c > 0$ keeps its shape and
divides its rate by $c$. The density of $cX$ at $y$ is $1/c$ times the density of $X$ at $y/c$, and for
the density $\frac{r^a}{\Gamma(a)} x^{a-1} e^{-rx}$ this is again a gamma density, with rate $r/c$. So
questions about $\Gamma(a, r)$ reduce to the case of rate $1$; for instance the mean $a/r$ and the
variance $a/r^2$ scale by $c$ and $c^2$.

## Statements

- [Scaling a gamma random variable](gamma-measure-map-const-mul.md)
