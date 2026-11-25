# Transport of the limit covariance along the adjoint flow

Let $V$ be a [limit covariance](is-limit-covariance.md) around $x$ from $V_0$, let $t \ge 0$, let
$x$ be continuous on $[0, t]$, and let $y_a$ and $y_b$ be continuous on $[0, t]$ and solve the
adjoint equation $y' = -DF(x)^{\mathsf T} y$ on $(0, t)$. Then

$$
\langle y_a(t), V(t)\, y_b(t) \rangle = \langle y_a(0), V_0\, y_b(0) \rangle +
\int_0^t \langle y_a(s), G(x(s))\, y_b(s) \rangle\, ds,
$$

with the [infinitesimal covariance](diffusion-matrix.md) $G$ and the [bilinear form](quad-form.md).
