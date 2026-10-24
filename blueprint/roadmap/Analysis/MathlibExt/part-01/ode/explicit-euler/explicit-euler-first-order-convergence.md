---
article_id: af_70932f8acc490810f716bd13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence
---

# Explicit euler first order convergence

Explicit Euler is first-order convergent: for a `C^2` right-hand side,
Lipschitz in the state, a true solution exists on `[t₀, T]` and the Euler
polygonal approximations have global error `O(h)` with a uniform constant.

Proof: clamp the time variable and use global Picard--Lindelöf for existence.  The local bound
above and Mathlib's discrete Grönwall inequality then give the first-order global estimate.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ode global exists of global lipschitz](../maximal-solution/ode-global-exists-of-global-lipschitz.md)
- [Exists explicit Euler local Truncation Error le](exists-explicit-euler-local-truncation-e.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.ExplicitEuler](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Ordinary differential equations`, entries `explicit Euler method`, `convergence` and `order` (unmapped); E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential Equations I, 2nd ed., Theorem I.7.3; stable ref https://en.wikipedia.org/wiki/Euler_method.
