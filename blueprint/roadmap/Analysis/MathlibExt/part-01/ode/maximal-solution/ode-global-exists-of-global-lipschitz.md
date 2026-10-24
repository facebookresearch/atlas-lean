---
article_id: af_c2e0a73ffafb0892d4528917
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
---

# Ode global exists of global lipschitz

Global existence and uniqueness for globally Lipschitz right-hand sides.

Proof: local Picard--Lindelöf solutions are continued using the Gronwall bound of Teschl's
Theorem 2.17 and the extension criterion of Lemma 2.14.  Time reversal supplies the
negative-time solution, and global Gronwall uniqueness identifies every solution with the glued
one.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Has Deriv At piecewise union of eq On](has-deriv-at-piecewise-union-of-eq-on.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.MaximalSolution](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entry `maximal solutions` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.2; stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
