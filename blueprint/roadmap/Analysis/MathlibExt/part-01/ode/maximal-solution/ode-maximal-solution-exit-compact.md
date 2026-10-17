---
article_id: af_af91460db8d3e3bb8fff55a0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact
---

# Ode maximal solution exit compact

Maximal solutions exit compacts: an ODE whose right-hand side is locally
Lipschitz in the state variable, locally uniformly in time, on an open set
admits a solution on a maximal open interval which, at each end, eventually
leaves every compact subset of the domain.

Proof: local Picard--Lindelöf solutions are glued by uniqueness into Teschl's maximal solution
(Theorem 2.13).  A compactly recurrent finite endpoint extends by Lemma 2.14, giving the two exit
statements of Corollaries 2.15--2.16.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Has Deriv At piecewise union of eq On](has-deriv-at-piecewise-union-of-eq-on.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.MaximalSolution](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entries `maximal solutions` and `exit theorem of a compact subspace` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.4.
