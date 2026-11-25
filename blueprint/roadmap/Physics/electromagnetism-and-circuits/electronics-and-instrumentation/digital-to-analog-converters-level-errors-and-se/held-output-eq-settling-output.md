# On a holding interval, the output is the explicit settling output

Let $\tau > 0$ and $u$ be real numbers, let $t_0 < t_1$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = u - y(s)$ (a first-order stage driven by the held level
$u$). Then for every $t \in [t_0, t_1]$, right endpoint included,

$$y(t) = u + (y(t_0) - u)\, e^{-(t - t_0)/\tau},$$

the [settling output](settling-output.md) with initial value $y(t_0)$. No derivative is assumed at
the endpoints. A discontinuous reset of the output, or a held level that varies on the interval, is
outside these hypotheses.
