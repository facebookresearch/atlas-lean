/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IndustrialOrganization.Monopsony
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.IndustrialOrganization.Monopsony` (Atlas EC17.T04). -/

namespace MathlibExtTest.Economics.IndustrialOrganization.Monopsony

open MathlibExt.Economics.Monopsony

/-- Test model: `α = 0, β = 1, γ = 12, δ = 0`. -/
def m : Model :=
  { α := 0, β := 1, γ := 12, δ := 0,
    β_pos := one_pos, δ_nonneg := le_rfl, α_lt_γ := by norm_num }

lemma monopsonyEmployment_eq : monopsonyEmployment m = 6 := by
  show (12 - 0) / (0 + 2 * 1) = (6 : ℝ)
  norm_num

lemma monopsonyWage_eq : monopsonyWage m = 6 := by
  have hLm : monopsonyEmployment m = 6 := monopsonyEmployment_eq
  unfold monopsonyWage supplyWage
  rw [hLm]
  show (0 : ℝ) + 1 * 6 = 6
  norm_num

/-- Minimum wage `w = 9` lies in the interval; `L = 9` maximizes profit. -/
example : IsMinWageEmployment m 9 9 := by
  have hsupply : ∀ L' : ℝ, supplyWage m L' = L' := by
    intro L'
    show (0 : ℝ) + 1 * L' = L'
    ring
  have hrev : ∀ L' : ℝ, revenue m L' = 12 * L' := by
    intro L'
    show (12 : ℝ) * L' - 0 / 2 * L' ^ 2 = 12 * L'
    ring
  have h9 : minWageProfit m 9 9 = 27 := by
    have hs9 : supplyWage m 9 = 9 := hsupply 9
    have hr9 : revenue m 9 = 108 := by
      rw [hrev 9]
      norm_num
    unfold minWageProfit
    rw [hs9, hr9, max_self]
    norm_num
  refine ⟨by norm_num, ?_⟩
  intro L' hL'
  rw [h9]
  unfold minWageProfit
  rw [hrev L', hsupply L']
  by_cases hle : L' ≤ 9
  · rw [max_eq_left hle]
    linarith
  · have hlt : 9 < L' := lt_of_not_ge hle
    rw [max_eq_right (le_of_lt hlt)]
    have e := mul_nonneg (show (0 : ℝ) ≤ L' - 9 by linarith)
      (show (0 : ℝ) ≤ L' - 3 by linarith)
    linarith

/-- Existence on the interval, via the pinned theorem. -/
example : ∃ L, IsMinWageEmployment m 9 L := by
  apply exists_isMinWageEmployment m
  rw [monopsonyWage_eq]
  norm_num

/-- Every maximizer at `w = 9` exceeds monopsony employment `6`. -/
example : ∀ L : ℝ, IsMinWageEmployment m 9 L → 6 < L := by
  intro L hL
  have hLm : monopsonyEmployment m = 6 := monopsonyEmployment_eq
  have hmw : monopsonyWage m = 6 := monopsonyWage_eq
  have h := monopsonyEmployment_lt_of_isMinWageEmployment m
    (show monopsonyWage m < 9 by rw [hmw]; norm_num)
    (show (9 : ℝ) < m.γ - m.δ * monopsonyEmployment m by
      rw [hLm]
      show (9 : ℝ) < 12 - 0 * 6
      norm_num)
    hL
  rw [hLm] at h
  exact h

/-- Unregulated profit peaks at monopsony employment: `36` at `L = 6` beats `32` at `L = 4`. -/
example : profit m 4 ≤ profit m (monopsonyEmployment m) := by
  have hLm : monopsonyEmployment m = 6 := monopsonyEmployment_eq
  have h6 : profit m 6 = 36 := by
    show (12 : ℝ) * 6 - 0 / 2 * 6 ^ 2 - (0 + 1 * 6) * 6 = 36
    norm_num
  have h4 : profit m 4 = 32 := by
    show (12 : ℝ) * 4 - 0 / 2 * 4 ^ 2 - (0 + 1 * 4) * 4 = 32
    norm_num
  have h := profit_le_profit_monopsonyEmployment m 4
  rw [hLm, h6, h4] at h ⊢
  exact h

end MathlibExtTest.Economics.IndustrialOrganization.Monopsony
