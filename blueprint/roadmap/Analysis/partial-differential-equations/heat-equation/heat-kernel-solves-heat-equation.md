# The Gaussian heat kernel solves the heat equation

Let $f\colon \mathbb{R} \to \mathbb{R}$
be continuous and bounded, and let $u(t, x)$ be the heat solution of $f$. Then for every
$t > 0$ and every $x \in \mathbb{R}$ there are a function $u_x\colon \mathbb{R} \to \mathbb{R}$
and a real number $u_{xx}$ such that $u(t, \cdot)$ has derivative $u_x(y)$ at every
$y \in \mathbb{R}$, $u_x$ has derivative $u_{xx}$ at $x$, and $u(\cdot, x)$ has derivative
$u_{xx}$ at $t$; that is, $\partial_t u = \partial_x^2 u$ on $(0, \infty) \times \mathbb{R}$.
Moreover, for every $x \in \mathbb{R}$, $u(t, x) \to f(x)$ as $t \to 0$ from above.

## Informally uses

- [The heat kernel solves the heat equation](heat-kernel-has-deriv-at-time-eq-laplaci.md): the
  identity $\partial_t \Phi = \partial_x^2 \Phi$ for the kernel, differentiated under the integral
  sign.
- [The heat kernel has total mass one](integral-heat-kernel.md): the approximate-identity argument
  for the initial trace.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf),
  Theorem 4.3 (for bounded continuous initial data on $\mathbb{R}^n$).
- Classical heat-equation theory. Problem `heat_kernel_solves_heat_equation` of the lean-eval benchmark.
