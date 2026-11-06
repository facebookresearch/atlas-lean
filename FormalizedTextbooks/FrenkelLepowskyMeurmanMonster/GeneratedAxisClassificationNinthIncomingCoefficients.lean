/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingPhaseCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingCoefficientCertificates

/-! Every original incoming odd-column coefficient retains its actual source and central phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual middle odd-short column has its certified full signed numerator over sixteen. -/
theorem generatedNinth_middle_incoming_coefficient (d : Fin 2048) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (generatedNinthIncomingTargetIndex d) =
        (generatedNinthIncomingCoefficient d : ℝ) / 16 := by
  rw [generatedFourth_local_short, generatedNinth_incoming_operator,
    generatedNinthIncomingShortNumerator_actual]
  have hc := generatedNinth_incoming_coefficient_certificate d
  by_cases h : generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) = 0
  · rw [h, mul_zero] at hc
    simp only [h, Int.cast_zero, zero_div, mul_zero, ← hc]
  · have hp : localShortPhase generatedNinthLocalFiber
        (generatedNinthIncomingShortIndex (generatedNinthIncomingSource d)) =
          generatedNinthIncomingPhase d := by
      rw [generatedNinth_incoming_short_phase]
      exact generatedNinth_incoming_phase_certificate d h
    rw [hp]
    have he : (if generatedNinthIncomingPhase d = 0 then (1 : ℝ) else -1) *
        (generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) : ℝ) =
          (generatedNinthIncomingCoefficient d : ℝ) := by
      exact_mod_cast hc
    change (if generatedNinthIncomingPhase d = 0 then (1 : ℝ) else -1) *
      ((generatedNinthIncomingShortNumerator (generatedNinthIncomingSource d) : ℝ) / 16) = _
    rw [← mul_div_assoc, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
