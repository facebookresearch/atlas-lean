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
`D` there; positivity of the denominator for `n = 4`.
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

/-- `c₁(4) = 5 / 9 - 6 / 11 = 1 / 99`. -/
example : tajimaC1 4 = 1 / 99 := by
  simp [tajimaC1, tajimaB1, tajimaA1, Finset.sum_Ico_succ_top]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaD
