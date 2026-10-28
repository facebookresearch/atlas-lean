/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhasePacked

/-! An executable integer numerator for every genuine sixth-axis tensor coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both incoming spin signs are read from the checked complete original phase vector. -/
def generatedSixthFinalTensorPackedNumerator (n : Fin 4096) (j : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let d := spinDictionaryCode t
  let s : ℤ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  8 * nortonUIntegerSign (t 11) * s * generatedSixthMiddleOddPackedNumerator d j -
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * s *
      generatedSixthFrameVectorData 8 0 j *
        (generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ -
          generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩)

/-- The executable numerator equals the previously proved full original tensor numerator. -/
theorem generatedSixth_final_tensor_packed_numerator (n : Fin 4096) (j : Fin 24) :
    generatedSixthFinalTensorPackedNumerator n j = generatedSixthFinalTensorNumerator n j := by
  simp only [generatedSixthFinalTensorPackedNumerator, generatedSixthFinalTensorNumerator,
    generatedSixth_packed_spin_phase]

/-- Every genuine tensor coordinate is the executable checked numerator over thirty-two root two. -/
theorem generatedSixth_final_tensor_packed (n : Fin 4096) (j : Fin 24) :
    (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) j =
      (generatedSixthFinalTensorPackedNumerator n j : ℝ) / (32 * Real.sqrt 2) := by
  rw [generatedSixth_final_tensor_packed_numerator]
  exact generatedSixth_final_tensor_integer n j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
