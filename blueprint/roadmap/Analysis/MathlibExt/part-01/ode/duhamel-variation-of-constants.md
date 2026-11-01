---
article_id: af_2da613509218140980412e73
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
---

# Duhamel

Duhamel's formula (variation of constants): for a bounded linear operator
`A` and continuous forcing `b`, the function built from the operator
exponential solves `x' = A x + b` from `x₀`, and it is the unique solution.

Proof: Factor the propagator by the commuting exponential group law, differentiate the
integrating-factor primitive, and apply global Lipschitz uniqueness. This follows Teschl,
Sections 3.2 and 3.4, formula (3.48) and Theorem 3.12 / (3.97).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.Duhamel](../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entry `method of constant variation (Duhamel's formula)` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.2; stable ref https://en.wikipedia.org/wiki/Duhamel%27s_principle.
