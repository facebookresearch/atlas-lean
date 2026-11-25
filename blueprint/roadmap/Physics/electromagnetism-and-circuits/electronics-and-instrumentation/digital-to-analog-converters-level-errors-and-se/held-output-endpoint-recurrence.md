# Output at the end of a holding interval

Let $\tau > 0$ and $u$ be real numbers, let $t_0 < t_1$, and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = u - y(s)$ (a first-order stage driven by the held level
$u$). Then the output at the right endpoint is

$$y(t_1) = u + (y(t_0) - u)\, e^{-(t_1 - t_0)/\tau},$$

the initial mismatch decayed over the whole interval. With continuity across the junction this is
the initial value of the next holding interval
([settling across a change of held level](held-output-two-intervals.md)).
