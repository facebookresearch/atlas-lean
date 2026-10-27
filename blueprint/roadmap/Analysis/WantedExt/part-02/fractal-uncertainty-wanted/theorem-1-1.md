---
article_id: af_2f795341b2461ff98bd3a658
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.FractalUncertaintyWanted.FractalUncertainty.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1:

Let `ν > 0` and assume that
- `X ⊆ [−1,1]ᵈ` is `ν`-porous on balls from scales `h` to `1`, and
- `Y ⊆ [−h⁻¹,h⁻¹]ᵈ` is `ν`-porous on lines from scales `1` to `h⁻¹`.
Then there exist `β,C > 0` depending only on `ν` and `d` such that for all `f ∈ L²(ℝᵈ)`,
`supp (𝓕 f) ⊆ Y => ‖f * 1_X‖₂ ≤ C * h ^ β * ‖f‖₂`.
Note: We require `X` and `Y` to be measurable to make the statement more natural.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.FractalUncertaintyWanted](../../../../../sources/v2/WantedExt.md)
- A. Cohen, `Fractal uncertainty in higher dimensions`, Annals of Math, 202 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-202-1-FractalUncertainty.lean Via leanprover/lean-eval@38361be, problem `annals_fractal_uncertainty`.
