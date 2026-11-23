# Uniqueness of the Green integral solution of L u = −g

Let $b$ and $a$ define a [regular diffusion](is-regular-diffusion.md) ($a$ positive and continuous
on $(0, 1)$, $b/a$ continuous on $(0, 1)$ and integrable on $[0, 1]$; accessibility of the endpoints
is not part of this), with [scale function](scale-function.md) $S$ and
[scale density](scale-density.md) $\psi$. Let $g$ be continuous on $(0, 1)$ and such that, for every
$q \in (0, 1)$, the function $S g/(a\psi)$ is integrable on $[0, q]$ and $(S(1) - S)\, g/(a\psi)$ is
integrable on $[q, 1]$. Suppose that the Green integral

$$v(q) = \int_0^1 G(q, x)\, g(x)\, dx,$$

with the [Green's function](green-function.md) $G$, is continuous on $[0, 1]$ and differentiable on
$(0, 1)$ with derivative differentiable on $(0, 1)$. Let $u$ be continuous on $[0, 1]$ and
differentiable on $(0, 1)$ with derivative differentiable on $(0, 1)$, with $(L_{b,a} u)(x) = -g(x)$
for every $x \in (0, 1)$, where $L_{b,a}$ is the [backward generator](diffusion-generator.md), and
$u(0) = u(1) = 0$. Then $u(x) = v(x)$ for every $x \in [0, 1]$.
