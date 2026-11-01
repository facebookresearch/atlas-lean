---
article_id: af_5ed867807b64ae4592df2337
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.FiniteTimeSingularityWanted.FiniteTimeSingularity.theorem_1
---

# Theorem 1

Statement of Theorem 1:

There exist an `α > 0` and a divergence-free and odd `u₀ ∈ C^{1,α}(ℝ³)` with initial vorticity
`‖∇ × u₀‖ ≤ C/(‖x‖^α + 1)` for some constant `C > 0` so that the unique local odd solution to
(1.1)-(1.3) belonging to the class `C^{1,α}(ℝ³ × [0,1))` satisfies

`lim_{t → 1⁻} ∫ s ∈ [0,t], ‖(∇ × u)(·, s)‖_{L∞} ds = +∞`.

Note: As mentioned in the paper, uniqueness of solutions up until any time `T` (when they exist)
was already known, so the formal statement only asks for existence.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.FiniteTimeSingularityWanted](../../../../../sources/v2/WantedExt.md)
- T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-FiniteTimeSingularity.lean Via leanprover/lean-eval@38361be, problem `annals_finite_time_singularity`.
