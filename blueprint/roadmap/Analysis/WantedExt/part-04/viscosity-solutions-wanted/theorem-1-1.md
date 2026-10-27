---
article_id: af_6b63f4b25f7edfce657aa056
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.ViscositySolutionsWanted.ViscositySolutions.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1:

For any `N`, finite dimensional inner product space `E` of dimension at least `2`,
(positive) masses `m : ℝᴺ`, any initial condition `x₀ : Eᴺ`, any configuration `a : Eᴺ`
without collisions such that `‖a‖ₘ = 1`, and any (positive) energy constant `h`, there exists
(hyperbolic) motions `x : ℝ → Eᴺ` such that they form a solution to the N-body problem with
masses `m`, satisfy the initial condition `x(0) = x₀`, are without collisions for all `t > 0`,
and satisfy

`x(t) = √(2h)ta + o(t)` as `t → ∞`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.ViscositySolutionsWanted](../../../../../sources/v2/WantedExt.md)
- E. Maderna and A. Venturelli, `Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-ViscositySolutions.lean Via leanprover/lean-eval@38361be, problem `annals_viscosity_solutions`.
