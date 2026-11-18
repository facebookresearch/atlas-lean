# Constant solutions and constant preservation of g-expectations

Let $(\Omega, P)$ be a probability space, $F$ a filtration, and $B$ a Brownian motion adapted to $F$ whose
increments $B_t - B_s$ ($s \le t$) are independent of $F_s$. Let $T \ge 0$, $c \in \mathbb{R}$, and $g$ a
generator with $g(t, \omega, c, 0) = 0$ for all $t, \omega$. Then $(Y, Z) = (c, 0)$ is a
[solution](is-bsdesolution.md) of the BSDE with generator $g$ and terminal value $c$. With uniqueness of
solutions, this is the property $\mathcal E^g[c] = c$ of Peng's g-expectation, defined for generators with
$g(\cdot, y, 0) \equiv 0$.

## Background

- [Sublinear expectation](../../foundations/sublinear-expectations-and-model-uncertainty/is-sublinear-expectation.md):
  a g-expectation is a monotone, constant preserving nonlinear expectation; its uncertain models
  are all absolutely continuous with respect to the Wiener measure, a limitation that Peng's
  G-expectation removes (Peng, Section 2, first paragraph).

## Sources

- S. Peng, *Backward stochastic differential equation, nonlinear expectation and their applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I, Hindustan Book Agency, 2010, 393–432, Section 1.6, equation (1.19) and the sentence after it.
