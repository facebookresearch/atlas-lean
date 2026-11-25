# Gravity and drag losses in rocket ascent

This node covers the velocity budget of a rocket in planar flight. Let $m(t) > 0$ be continuously differentiable and nonincreasing on
$[0, t_b]$, let the thrust along the velocity be $T = -v_e\,\dot m$ with constant exhaust speed $v_e > 0$, and let the speed $v$ satisfy

$$\dot v = \frac{T - D(t)}{m(t)} - g\sin\gamma(t)$$

with drag $D \ge 0$, constant gravitational acceleration $g > 0$ and flight-path angle $\gamma$, all continuous. Then

$$v(t_b) - v(0) = v_e\ln\frac{m(0)}{m(t_b)} - \int_0^{t_b} g\sin\gamma\,dt - \int_0^{t_b}\frac{D}{m}\,dt,$$

so the ideal increment is reduced by the gravity loss and the drag loss, both nonnegative when $0 \le \gamma \le \pi/2$.

## Expansion

A good expansion states the tangential equation of motion as a model input with its sign conventions, integrates it, and
records when each loss is nonnegative. Optimizing the steering program to minimize losses is a separate node, as is the ideal increment in a
field-free space.

## Sources

- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 7th edition, Wiley, 2000, for flight performance and gravity losses.
