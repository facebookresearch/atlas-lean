# Local truncation error of the explicit Euler method

Let $E$ be a real Banach space, let
$t_0 < T$, let $f : \mathbb{R} \times E \to E$ be $C^2$, let $x_0 \in E$, and let
$x : \mathbb{R} \to E$ satisfy $x(t_0) = x_0$ and $x'(t) = f(t, x(t))$ for every
$t \in [t_0, T]$. Then there is a constant $C$ such that
$\|x(t + h) - (x(t) + h f(t, x(t)))\| \le C h^2$ for every $h \in (0, T - t_0]$ and every
$t \in [t_0, T]$ with $t + h \le T$.

Proof: differentiate the velocity by the chain rule, bound that derivative on the compact time
interval, and apply the mean value inequality twice.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Ordinary differential equations`, entry `consistency` (unmapped); E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential Equations I, 2nd ed., Section I.7.
