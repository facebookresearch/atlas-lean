# Green function, occupation times and mean exit times of a one-dimensional diffusion

Under the hypotheses of [the scale function and exit probabilities](scale-function-and-exit-probabilities-for-one-di.md), let $m(dy) = 2\, dy / (a(y)\, s'(y))$ be the speed measure and

$$G(x, y) = \frac{\bigl(s(x \wedge y) - s(l)\bigr)\bigl(s(r) - s(x \vee y)\bigr)}{s(r) - s(l)}$$

the Green kernel, with $\tau$ the exit time from $(l, r)$. Then for every nonnegative measurable $g$,

$$\mathbb{E}_x \int_0^\tau g(X_s)\, ds = \int G(x, y)\, g(y)\, m(dy) \in [0, \infty].$$

If in addition the weighted integral $\int_l^r (s(y) - s(l))(s(r) - s(y))\, m(dy)$ is finite, then $\mathbb{E}_x \tau = \int G(x, y)\, m(dy) < \infty$ and the identity holds for bounded signed $g$. Finite total mass of $m$ is not required.

## Depends on

- [Scale function and exit probabilities for one-dimensional diffusions (process level)](scale-function-and-exit-probabilities-for-one-di.md)

## Expansion

1. The identity for nonnegative $g$, then for bounded signed $g$ under the weighted integrability.
2. Checks: Brownian motion on $(0, 1)$ has $\mathbb{E}_x \tau = x(1 - x)$. For the neutral Wright–Fisher diffusion, $s(y) = y$ and $m(dy) = 2\, dy/(y(1 - y))$ has infinite total mass, but $\int_0^1 y(1 - y)\, m(dy) = 2 < \infty$, so the real-valued clause applies.
3. Signed $g$ without the weighted integrability is excluded from the real-valued claim.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981), <https://shop.elsevier.com/books/a-second-course-in-stochastic-processes/karlin/978-0-08-057050-1> (Green function and speed measure).
