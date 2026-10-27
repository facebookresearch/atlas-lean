---
article_id: af_275c5b42dd3d8983037d81c6
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.HessianEstimatesWanted.HessianEstimates.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1:

There exists a function `C : ℝ≥0∞ → ℝ` such that if `u : ℝ⁴ → ℝ` satisfies the following properties:
* `u` is smooth on `B₁(0)`,
* `‖u‖_{C¹(B₁(0))} < ∞` (the definition of this norm is given above), and
* for all `x ∈ B₁(0)`, `(Δ u) x > 0` and `(σ₂ D²u) x = 1`,
then `‖D² u 0‖_F ≤ C(‖u‖_{C¹})`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.HessianEstimatesWanted](../../../../../sources/v2/WantedExt.md)
- R. Shankar and Y. Yuan, `Hessian estimates for the sigma-2 equation in dimension four`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-HessianEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_hessian_estimates`.
