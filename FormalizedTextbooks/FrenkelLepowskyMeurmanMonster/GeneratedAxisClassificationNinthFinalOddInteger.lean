/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOddTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleTensor

/-! All final odd-short coordinates retain the complete original nine-factor integer spin word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact final odd-short numerator before any finite numerical cache is substituted. -/
def generatedNinthFinalOddInteger (d : Fin 2048) (i : Fin 24) : ℤ :=
  generatedNinthMiddleTensorInteger
      (nortonUIntegerLabel (golayLabelCoefficients ⟨d.val, by omega⟩)) i +
    generatedNinthMiddleTensorInteger
      (nortonUIntegerLabel (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) i

/-- Every final odd-short coefficient of the literal axis has its exact signed numerator. -/
theorem generatedNinth_final_odd_integer (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedNinthFinalOddInteger d i : ℝ) / 65536 := by
  rw [generatedNinthAxis_local_expression, generatedNinth_final_triality_odd_coordinate,
    generatedNinth_middle_tensor_integer, generatedNinth_middle_tensor_integer]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [generatedNinthFinalOddInteger, Int.cast_add]
  field_simp [hs]
  rw [hsq]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
