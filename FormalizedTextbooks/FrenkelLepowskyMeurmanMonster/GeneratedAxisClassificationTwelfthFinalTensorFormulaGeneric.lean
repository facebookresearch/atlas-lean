/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSpatialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Every original root-nine tensor coordinate retains both genuine triality source terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact incoming odd coefficient uses the complete original source short dictionary. -/
def generatedTwelfthIncomingOddCoefficient (d : Fin 2048) (i : Fin 24) : ℤ :=
  generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inr (d, i)))

/-- All eight genuine incoming factors retain every original spin and spatial coordinate. -/
def generatedTwelfthIncomingTensorNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ r : Fin 8, generatedTwelfthTensorSourceSpinNumerator 3 r n *
    generatedTwelfthTensorSourceSpatialNumerator 3 r i

/-- The complete original normalized XYZ numerator at any spin label and spatial column. -/
def generatedTwelfthFinalTensorSourceInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let parker := nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  (if n.val < 2048 then 4 else -4) * sigma * generatedTwelfthIncomingOddCoefficient d i +
    sigma * parker * (generatedTwelfthIncomingTensorNumerator ⟨d.val, by omega⟩ i -
      generatedTwelfthIncomingTensorNumerator ⟨d.val + 2048, by omega⟩ i)

/-- The integer formula retains the actual real source signs on both Omega rows. -/
theorem generatedTwelfth_final_tensor_source_integer_real (t : SpinIndex) (i : Fin 24) :
    (generatedTwelfthFinalTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) =
      4 * qSign (t 11) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        (generatedTwelfthIncomingOddCoefficient (spinDictionaryCode t) i : ℝ) +
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        ((generatedTwelfthIncomingTensorNumerator ⟨(spinDictionaryCode t).val, by omega⟩ i : ℝ) -
          (generatedTwelfthIncomingTensorNumerator
            ⟨(spinDictionaryCode t).val + 2048, by omega⟩ i : ℝ)) := by
  obtain h | h := spinDictionaryIndex_cases t
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_low, golayLabel_low_last,
      qSign_zero, mul_one]
    simp only [generatedTwelfthFinalTensorSourceInteger,
      Nat.mod_eq_of_lt (spinDictionaryCode t).isLt, (spinDictionaryCode t).isLt,
      ite_true, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_high, golayLabel_high_last,
      qSign_one]
    have hm : ((spinDictionaryCode t).val + 2048) % 2048 =
        (spinDictionaryCode t).val := by omega
    have hn : ¬ (spinDictionaryCode t).val + 2048 < 2048 := by omega
    simp only [generatedTwelfthFinalTensorSourceInteger, hm, hn, ite_false,
      Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
    split_ifs <;> ring

/-- Exact original incoming packets determine the complete outgoing normalized tensor formula. -/
theorem generatedTwelfth_final_tensor_source_generic_actual
    (hcache : ∀ r : GriessShortIndex, generatedAxisGlobalFifthRoot09Packet.2.1 r =
      (generatedTwelfthIncomingShortCoefficient r : ℝ) / 16)
    (htensor : ∀ (t : SpinIndex) (i : Fin 24),
      generatedAxisGlobalFifthRoot09Packet.2.2 t i =
        (generatedTwelfthIncomingTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (32 * Real.sqrt 2))
    (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedTwelfthAxis).2.2 t i =
      (generatedTwelfthFinalTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) := by
  rw [generatedTwelfth_final_tensor_source_integer_real, generatedTwelfth_tensor]
  change 64 * Real.sqrt 2 * generatedAxisGlobalRawTrialityTensor
    generatedAxisGlobalFifthRoot09Packet t i = _
  unfold generatedAxisGlobalRawTrialityTensor
  simp only [trialityYTensor, ite_true, mul_one]
  rw [hcache, htensor, htensor]
  simp only [generatedTwelfthIncomingOddCoefficient, nortonUIntegerLabel_coeff]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
