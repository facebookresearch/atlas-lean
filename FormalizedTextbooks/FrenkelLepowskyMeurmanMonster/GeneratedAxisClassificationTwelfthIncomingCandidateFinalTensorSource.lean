/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorCertificates

/-! The entire actual candidate tensor is bound to the retained complete integer input. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every actual outgoing candidate tensor coefficient equals the complete retained input.
The normalization includes both the original short and genuine incoming tensor terms. -/
theorem generatedTwelfth_candidate_final_tensor_actual (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.2 t i =
      (generatedTwelfthSpinTensorInputInteger (nortonUIntegerLabel t) i : ℝ) := by
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have ht (u : SpinIndex) (j : Fin 24) :
      (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
        generatedFifthAxis)).2.2 u j =
        (generatedTwelfthCandidateIncomingTensorNumerator (nortonUIntegerLabel u) j : ℝ) /
          (64 * Real.sqrt 2) := by
    apply (eq_div_iff (by positivity : (64 : ℝ) * Real.sqrt 2 ≠ 0)).mpr
    simpa only [generatedTwelfthCandidateIncomingTensorNumerator, mul_comm] using
      generatedTwelfth_incoming_candidate_tensor_actual u j
  have h := generatedTwelfth_candidate_final_tensor_generic_actual
    generatedTwelfth_incoming_short_actual ht t i
  rw [generatedTwelfth_candidate_final_tensor_input, Int.cast_mul, Int.cast_ofNat] at h
  nlinarith [h]

/-- The exact complete source tensor is a scalar multiple of the retained integer tensor. -/
theorem generatedTwelfth_candidate_final_tensor_source :
    (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.2 =
      (1 / (64 * Real.sqrt 2) : ℝ) •
        (fun u j => (generatedTwelfthSpinTensorInputInteger (nortonUIntegerLabel u) j : ℝ)) := by
  ext u j
  have h := generatedTwelfth_candidate_final_tensor_actual u j
  change _ = (1 / (64 * Real.sqrt 2)) * _
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  nlinarith [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
