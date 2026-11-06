/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliMiddleNumeric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor

/-! All24 tensor columns retain both exact original XYZ source contributions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original normalized XYZ numerator at any spin label and spatial column. -/
def generatedNinthLowerTensorSourceInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let parker := nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  (if n.val < 2048 then 4 else -4) * sigma * generatedNinthLowerIncomingCoefficient d i +
    sigma * parker * (generatedNinthMiddleNumerator ⟨d.val, by omega⟩ i -
      generatedNinthMiddleNumerator ⟨d.val + 2048, by omega⟩ i)

/-- The integer formula retains the actual real source signs on both Omega rows. -/
theorem generatedNinth_lower_tensor_source_integer_real (t : SpinIndex) (i : Fin 24) :
    (generatedNinthLowerTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) =
      4 * qSign (t 11) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        (generatedNinthLowerIncomingCoefficient (spinDictionaryCode t) i : ℝ) +
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        ((generatedNinthMiddleNumerator ⟨(spinDictionaryCode t).val, by omega⟩ i : ℝ) -
          (generatedNinthMiddleNumerator
            ⟨(spinDictionaryCode t).val + 2048, by omega⟩ i : ℝ)) := by
  obtain h | h := spinDictionaryIndex_cases t
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_low, golayLabel_low_last,
      qSign_zero, mul_one]
    simp only [generatedNinthLowerTensorSourceInteger,
      Nat.mod_eq_of_lt (spinDictionaryCode t).isLt, (spinDictionaryCode t).isLt,
      ite_true, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_high, golayLabel_high_last,
      qSign_one]
    have hm : ((spinDictionaryCode t).val + 2048) % 2048 =
        (spinDictionaryCode t).val := by omega
    have hn : ¬ (spinDictionaryCode t).val + 2048 < 2048 := by omega
    simp only [generatedNinthLowerTensorSourceInteger, hm, hn, ite_false,
      Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
    split_ifs <;> ring

/-- Every actual normalized tensor coordinate has its complete original integer XYZ formula. -/
theorem generatedNinth_lower_tensor_source_generic_actual
    (hcache : ∀ r : GriessShortIndex,
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
        generatedFifthAxis)).2.1 r =
          (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16)
    (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t i =
      (generatedNinthLowerTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) := by
  rw [generatedNinth_lower_tensor_source_integer_real,
    generatedNinthAxis_local_expression, generatedSixth_triality_tensor_coordinate]
  simp only [trialityYTensor, ite_true, mul_one]
  rw [hcache,
    generatedNinth_middle_numeric, generatedNinth_middle_numeric]
  simp only [generatedNinthLowerIncomingCoefficient, nortonUIntegerLabel_coeff]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
