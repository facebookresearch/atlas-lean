---
article_id: af_854018baf4f4a7300eb372c9
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted.EquiangularLinesFixedAngle.theorem_1_2
---

# Theorem 1 2

Statement of Theorem 1.2 (Main theorem):

Fix `α ∈ (0, 1)`. Let `λ = (1 − α)/(2α)` and `k = k(λ)` be its spectral radius order.
The maximum number `N_α(d)` of equiangular lines in `ℝᵈ` with common angle `arccos α` satisfies
(a) `N_α(d) = ⌊k(d − 1)/(k − 1)⌋` for all sufficiently large `d > d₀(α)` if `k < ∞`;
(b) `N_α(d) = d + o(d)` as `d → ∞` if `k = ∞`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.EquiangularLinesFixedAngleWanted](../../../../../sources/v2/WantedExt.md)
- Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-EquiangularLinesFixedAngle.lean Via leanprover/lean-eval@38361be, problem `annals_equiangular_lines_fixed_angle`.
