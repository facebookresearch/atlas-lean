---
article_id: af_bcaded79c367ea5ae92a21c7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted.fundamental_matrix_linear_system
---

# Fundamental matrix linear system

Fundamental matrix of a linear ODE system: for continuous `A`, there is a
matrix solution `Φ` of `Φ' = A Φ` with `Φ t₀ = 1`, everywhere invertible,
and every solution of `x' = A x` is a `Φ`-multiple of its initial value.

Proof: Global solutions are patched from clamped-time systems using Teschl, Theorem 3.9, then
assembled into the principal matrix solution of (3.83) and Theorem 3.10. Liouville's formula gives
invertibility as in (3.88)-(3.89).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Det of mul](det-of-mul.md)
- [Exists Unique has Deriv At eq continuous Linear Map](exists-unique-has-deriv-at-eq-continuous.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrix](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entry `linear differential systems` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.4; stable ref https://en.wikipedia.org/wiki/Fundamental_matrix_(linear_differential_equation).
