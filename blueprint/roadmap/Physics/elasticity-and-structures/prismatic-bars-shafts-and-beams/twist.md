# Twist and internal torque of a shaft fixed at one end

Let $GJ > 0$, let $L$ and $T$ be real numbers and $t \colon \mathbb{R} \to \mathbb{R}$, and let
$\varphi$ solve the [fixed-traction problem](is-fixed-traction-solution.md) on $[0, L]$ with
rigidity $GJ$, distributed load $t$ and end value $T$: in the shaft reading, $\varphi$ is the twist
of a circular shaft of torsional rigidity $GJ$, fixed against rotation at $x = 0$, under the
distributed torque $t$ and the end torque $T$ at $x = L$. Then for every $x \in [0, L]$

$$\varphi(x) = \int_0^x \frac{1}{GJ}\left(T + \int_y^L t(z)\, dz\right) dy, \qquad
GJ\, \varphi'(x) = T + \int_x^L t(y)\, dy,$$

with $\varphi'$ the derivative within $[0, L]$: the twist is the
[fixed-traction displacement](fixed-traction-displacement.md) with $k = GJ$, and the internal torque
$GJ\, \varphi'$ is the end torque plus the distributed torque carried between $x$ and $L$.
