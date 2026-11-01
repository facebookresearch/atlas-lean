/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOddTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliMiddleNumeric

/-! The checked original Pauli output gives every final physical odd-short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sum of the two checked original middle tensor numerators at the physical dictionary labels. -/
def generatedNinthFinalOddNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  generatedNinthMiddleNumerator
      (nortonUIntegerLabel (golayLabelCoefficients ⟨d.val, by omega⟩)) i +
    generatedNinthMiddleNumerator
      (nortonUIntegerLabel (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) i

/-- Every final odd-short coefficient is the quarter-weight signed checked numerator over64. -/
theorem generatedNinth_final_odd_numeric (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedNinthFinalOddNumerator d i : ℝ) / 64 := by
  rw [generatedNinthAxis_local_expression, generatedNinth_final_triality_odd_coordinate,
    generatedNinth_middle_numeric, generatedNinth_middle_numeric]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [generatedNinthFinalOddNumerator, Int.cast_add]
  field_simp [hs]
  rw [hsq]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
