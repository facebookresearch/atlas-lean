/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleOddArithmetic

/-! A finite integer formula for the entire canonical outgoing tensor packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- The low source label uses the same coefficient-eleven quotient as the actual dictionary. -/
def generatedSeventhXiTensorLow (d : Fin 4096) : Fin 2048 :=
  ⟨d.val % 2048, Nat.mod_lt _ (by decide)⟩

/-- The actual dictionary label agrees with the proved computable inverse source label. -/
theorem generatedSeventhXi_spin_dictionary_label (t : SpinIndex) :
    spinDictionaryLabel t = nortonUIntegerLabel t := by
  apply (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).injective
  simp only [spinDictionaryLabel, Equiv.apply_symm_apply]
  exact (nortonUIntegerLabel_inverse t).symm

/-- Reducing the computable label gives exactly the genuine dictionary low code. -/
theorem generatedSeventhXi_tensor_low (t : SpinIndex) :
    generatedSeventhXiTensorLow (nortonUIntegerLabel t) = spinDictionaryCode t := by
  simp only [generatedSeventhXiTensorLow, spinDictionaryCode,
    generatedSeventhXi_spin_dictionary_label]

/-- Each integer tensor coefficient retains the actual source sign and preferred-Q phases. -/
def generatedSeventhXiPlaneTensorNumerator (d : Fin 4096) (i : Fin 24) : ℤ :=
  let c := generatedSeventhXiTensorLow d
  (if (golayEncodedMask c.val).testBit i.val then -1 else 1) *
    (nortonUIntegerSign (golayLabelCoefficients d 11) * 8 *
        generatedSeventhXiMiddleOddNumerator c i -
      nortonUIntegerSign (golayMaskWeight (golayEncodedMask c.val) / 4 : ℕ) *
        generatedSeventhFrameVectorData 7 0 i *
        (generatedSeventhXiPlaneSpinInteger ⟨c.val, by omega⟩ -
          generatedSeventhXiPlaneSpinInteger ⟨c.val + 2048, by omega⟩))

/-- This integer formula equals every coordinate of the complete actual canonical tensor. -/
theorem generatedSeventhXiPlaneTensorNumerator_actual (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 t i =
      (generatedSeventhXiPlaneTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
        (32 * Real.sqrt 2) := by
  have h := generatedSeventhXi_canonical_axis_tensor t i
  dsimp only at h
  simp only [← generatedSeventhXiMiddleOddNumerator_eq] at h
  simpa only [generatedSeventhXiPlaneTensorNumerator, generatedSeventhXi_tensor_low,
    Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, nortonUIntegerSign_real, nortonUIntegerLabel_inverse] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
