---
article_id: af_82b79c7ca50b42df110672ad
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_local_truncation_error
---

# Explicit euler local truncation error

Explicit Euler consistency: one step from the exact solution has local
truncation error `O(h^2)`.

Proof: differentiate the velocity by the chain rule, bound that derivative on the compact time
interval, and apply the mean value inequality twice.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists explicit Euler local Truncation Error le](exists-explicit-euler-local-truncation-e.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.ExplicitEuler](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Ordinary differential equations`, entry `consistency` (unmapped); E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential Equations I, 2nd ed., Section I.7.
