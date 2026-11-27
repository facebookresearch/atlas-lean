# Ekeland variational principle

Let $(X, d)$ be a nonempty complete metric space, let
$f : X \to \mathbb{R}$ be lower semicontinuous and bounded below, and let $\varepsilon > 0$. If
$x_0 \in X$ satisfies $f(x_0) \le f(x) + \varepsilon$ for every $x \in X$, then there is
$x_\varepsilon \in X$ with $f(x_\varepsilon) \le f(x_0)$, $d(x_\varepsilon, x_0) \le 1$, and
$f(x_\varepsilon) < f(y) + \varepsilon\, d(x_\varepsilon, y)$ for every $y \ne x_\varepsilon$.

## Sources

- I. Ekeland, J. Math. Anal. Appl. 47 (1974), 324-353, DOI 10.1016/0022-247X(74)90025-0. It follows from `ekeland_variational_principle_general`; the instance `[Nonempty X]` is unused and keeps the source's shape.
