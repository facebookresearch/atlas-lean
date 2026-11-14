/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaD
import Mathlib.Tactic.NormNum

/-!
# Tests for Tajima's `D`

`D = 0` when `π = S / a₁`; the degenerate sample sizes `n = 2, 3` and the junk value of
`D` there; positivity of the denominator for `n = 4`;
`e₁(4)`, `e₂(4)` and their positivity, with `e₁(3) = e₂(3) = 0` showing the bound `n ≥ 4` is sharp.
-/

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaD

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- `D = 0` when the two estimators of `θ` agree. -/
example (n : ℕ) (S : ℝ) : tajimaD n (S / tajimaA1 n) S = 0 := by
  simp [tajimaD]

/-- For three genes the variance constants vanish, so `e₁ = e₂ = 0` and `D` takes Lean's
junk value `x / √0 = 0` (outside the domain `n ≥ 4`). -/
example (π S : ℝ) : tajimaD 3 π S = 0 := by
  simp [tajimaD, tajimaE1, tajimaE2, tajimaC1_three, tajimaC2_three]

/-- For two genes both constants vanish as well. -/
example : tajimaC1 2 = 0 ∧ tajimaC2 2 = 0 := ⟨tajimaC1_two, tajimaC2_two⟩

/-- For four genes and one segregating site the denominator is positive. -/
example : 0 < tajimaE1 4 * 1 + tajimaE2 4 * (1 * (1 - 1)) :=
  tajimaVarEstimator_pos le_rfl le_rfl

/-- `tajimaE1_pos` and `tajimaE2_pos` at the boundary `n = 4`. -/
example : 0 < tajimaE1 4 ∧ 0 < tajimaE2 4 := ⟨tajimaE1_pos le_rfl, tajimaE2_pos le_rfl⟩

/-- `e₁(4) = c₁(4) / a₁(4) = (1 / 99) / (11 / 6) = 2 / 363`, computed from the definitions. -/
example : tajimaE1 4 = 2 / 363 := by
  simp [tajimaE1, tajimaC1, tajimaB1, tajimaA1, Finset.sum_Ico_succ_top]
  norm_num

/-- `e₂(4) = c₂(4) / (a₁(4)² + a₂(4)) = (83 / 6534) / (170 / 36) = 83 / 30855`, computed from
the definitions. -/
example : tajimaE2 4 = 83 / 30855 := by
  simp [tajimaE2, tajimaC2, tajimaB2, tajimaA1, tajimaA2, Finset.sum_Ico_succ_top]
  norm_num

/-- The bound `n ≥ 4` in `tajimaE1_pos` and `tajimaE2_pos` is sharp: `e₁(3) = e₂(3) = 0`. -/
example : tajimaE1 3 = 0 ∧ tajimaE2 3 = 0 := by
  simp [tajimaE1, tajimaE2, tajimaC1_three, tajimaC2_three]

/-- `c₁(4) = 5 / 9 - 6 / 11 = 1 / 99`. -/
example : tajimaC1 4 = 1 / 99 := by
  simp [tajimaC1, tajimaB1, tajimaA1, Finset.sum_Ico_succ_top]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaD
