/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalTensorSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceFormula

/-! Ungated full original final tensor source formula; incoming tensor difference is retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete incoming C is bound to the original local word by its actual source certificate. -/
theorem generatedTenth_final_tensor_source_incoming_C
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis)).2.1 r =
      (generatedTenthFinalTensorSourceIncomingCQ r : ℝ) := by
  rw [generatedAxisGlobalFifthRoot02Packet_actual]
  simpa only [generatedTenthFinalTensorSourceIncomingCQ, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_ofNat] using generatedTenth_final_short_source_incoming_C hin r

/-- The full genuine eight-factor expression requires no incoming tensor cache calibration. -/
theorem generatedTenth_final_tensor_source_incoming_T (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis)).2.2 t i =
      (generatedTenthFinalTensorSourceIncomingTQ t i : ℝ) / Real.sqrt 2 := by
  rw [generatedAxisGlobalFifthRoot02Packet_actual]
  have h := generatedTenth_final_short_source_tensor_actual (nortonUIntegerLabel t) i
  simpa only [generatedTenthFinalTensorSourceIncomingTQ, nortonUIntegerLabel_inverse] using h

/-- Every one of the98304 actual final tensor coordinates retains both genuine triality source
terms; only the incoming C source certificate is required. -/
theorem generatedTenth_final_tensor_source_actual
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (k : Fin 4096) (i : Fin 24) :
    (griessConwayEncode generatedTenthAxis).2.2 (golayLabelCoefficients k) i =
      (generatedTenthFinalTensorSourceQ k i : ℝ) / (64 * Real.sqrt 2) := by
  have h := generatedAxisGlobalTrialityScaledTensorQ_actual
    (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis)
    generatedTenthFinalTensorSourceIncomingCQ generatedTenthFinalTensorSourceIncomingTQ
    (generatedTenth_final_tensor_source_incoming_C hin)
    generatedTenth_final_tensor_source_incoming_T (golayLabelCoefficients k) i
  rw [generatedTenthAxis_local_expression, generatedTenthLocal, h]
  unfold generatedTenthFinalTensorSourceQ
  push_cast
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]

/-- The complete actual outgoing numerator has exactly the original64 times sqrt2 scale. -/
theorem generatedTenth_final_tensor_source_scaled
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (k : Fin 4096) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedTenthAxis).2.2
      (golayLabelCoefficients k) i = (generatedTenthFinalTensorSourceQ k i : ℝ) := by
  rw [generatedTenth_final_tensor_source_actual hin k i]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
