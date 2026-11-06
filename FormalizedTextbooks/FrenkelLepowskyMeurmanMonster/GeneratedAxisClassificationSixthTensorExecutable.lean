/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorPacked

/-! Direct twelve-bit labels eliminate the noncomputable dictionary selector from exact checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine dictionary label is the lower eleven bits of the source spin label. -/
def generatedSixthTensorDictionary (n : Fin 4096) : Fin 2048 :=
  ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩

/-- The executable lower-bit label is the actual dictionary selector, on both spin halves. -/
theorem generatedSixth_tensor_dictionary (n : Fin 4096) :
    spinDictionaryCode (golayLabelCoefficients n) = generatedSixthTensorDictionary n := by
  let d := generatedSixthTensorDictionary n
  by_cases h : n.val < 2048
  · have hn : n = ⟨d.val, by omega⟩ := by
      apply Fin.ext
      exact (Nat.mod_eq_of_lt h).symm
    rw [hn, spinDictionaryCode_low]
    apply Fin.ext
    exact (Nat.mod_eq_of_lt d.isLt).symm
  · have hn : n = ⟨d.val + 2048, by omega⟩ := by
      apply Fin.ext
      dsimp [d, generatedSixthTensorDictionary]
      omega
    rw [hn, spinDictionaryCode_high]
    apply Fin.ext
    change d.val = (d.val + 2048) % 2048
    omega

/-- A wholly executable original tensor numerator with the actual dictionary identity proved. -/
def generatedSixthTensorExecutable (n : Fin 4096) (j : Fin 24) : ℤ :=
  let t := golayLabelCoefficients n
  let d := generatedSixthTensorDictionary n
  let s : ℤ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  8 * nortonUIntegerSign (t 11) * s * generatedSixthMiddleOddPackedNumerator d j -
    nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * s *
      generatedSixthFrameVectorData 8 0 j *
        (generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ -
          generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩)

/-- The executable expression retains the complete actual preferred signed tensor numerator. -/
theorem generatedSixth_tensor_executable_eq (n : Fin 4096) (j : Fin 24) :
    generatedSixthTensorExecutable n j = generatedSixthFinalTensorPackedNumerator n j := by
  simp only [generatedSixthTensorExecutable, generatedSixthFinalTensorPackedNumerator,
    generatedSixth_tensor_dictionary]

/-- All actual tensor coordinates have the proved executable integer value. -/
theorem generatedSixth_tensor_executable (n : Fin 4096) (j : Fin 24) :
    (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) j =
      (generatedSixthTensorExecutable n j : ℝ) / (32 * Real.sqrt 2) := by
  rw [generatedSixth_tensor_executable_eq]
  exact generatedSixth_final_tensor_packed n j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
