/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateBlocks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Complete candidate tensor coordinates retain both genuine triality source terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
-- The complete incoming candidate and source normalization retain their full construction spines.
set_option maxRecDepth 100000

/-- The integer formula retains the actual real source signs on both Omega rows. -/
theorem generatedTwelfth_candidate_final_tensor_integer_real (t : SpinIndex) (i : Fin 24) :
    (generatedTwelfthCandidateFinalTensorInteger (nortonUIntegerLabel t) i : ℝ) =
      8 * qSign (t 11) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        (generatedTwelfthCandidateIncomingOddCoefficient (spinDictionaryCode t) i : ℝ) +
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1 else 1) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        ((generatedTwelfthCandidateIncomingTensorNumerator ⟨(spinDictionaryCode t).val, by omega⟩ i : ℝ) -
          (generatedTwelfthCandidateIncomingTensorNumerator
            ⟨(spinDictionaryCode t).val + 2048, by omega⟩ i : ℝ)) := by
  obtain h | h := spinDictionaryIndex_cases t
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_low, golayLabel_low_last,
      qSign_zero, mul_one]
    simp only [generatedTwelfthCandidateFinalTensorInteger,
      Nat.mod_eq_of_lt (spinDictionaryCode t).isLt, (spinDictionaryCode t).isLt,
      ite_true, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
  · rw [h]
    simp only [nortonUIntegerLabel_coeff, spinDictionaryCode_high, golayLabel_high_last,
      qSign_one]
    have hm : ((spinDictionaryCode t).val + 2048) % 2048 =
        (spinDictionaryCode t).val := by omega
    have hn : ¬ (spinDictionaryCode t).val + 2048 < 2048 := by omega
    simp only [generatedTwelfthCandidateFinalTensorInteger, hm, hn, ite_false,
      Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_ofNat,
      Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
    split_ifs <;> ring

/-- Exact original incoming short coefficients and candidate tensors
determine the entire actual outgoing tensor formula. -/
theorem generatedTwelfth_candidate_final_tensor_generic_actual
    (hcache : ∀ r : GriessShortIndex, generatedAxisGlobalFifthRoot09Packet.2.1 r =
      (generatedTwelfthIncomingShortCoefficient r : ℝ) / 16)
    (htensor : ∀ (t : SpinIndex) (i : Fin 24),
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.2 t i =
        (generatedTwelfthCandidateIncomingTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (64 * Real.sqrt 2))
    (t : SpinIndex) (i : Fin 24) :
    128 * Real.sqrt 2 * (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.2 t i =
      (generatedTwelfthCandidateFinalTensorInteger (nortonUIntegerLabel t) i : ℝ) := by
  rw [generatedTwelfth_candidate_final_tensor_integer_real]
  change 128 * Real.sqrt 2 * (griessConwayEncode
    (sExtra (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis))).2.2 t i = _
  rw [generatedAxisGlobalRawTrialityFormula_actual]
  change 128 * Real.sqrt 2 * generatedAxisGlobalRawTrialityTensor
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)) t i = _
  unfold generatedAxisGlobalRawTrialityTensor
  simp only [trialityYTensor, ite_true, mul_one]
  rw [generatedTwelfth_incoming_candidate_source_blocks.2, hcache, htensor, htensor]
  simp only [generatedTwelfthCandidateIncomingOddCoefficient, nortonUIntegerLabel_coeff]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
