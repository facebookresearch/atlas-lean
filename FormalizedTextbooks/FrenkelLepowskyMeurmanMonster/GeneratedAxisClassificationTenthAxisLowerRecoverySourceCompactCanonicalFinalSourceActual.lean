/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactIncomingPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateGeneric

/-! New canonical compact-source endpoints. All proof bodies remain uncompiled drafts.
The complete incoming B calibration is explicit; original source tensor orientation is unused. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete canonical incoming tensor calibration, including all zero coordinates. -/
def GeneratedTenthSourceCompactCanonicalBCondition : Prop :=
  ∀ k i, generatedTenthSourceCompactIncomingPacket.2.2 (golayLabelCoefficients k) i =
    (generatedTenthIncomingTensorPackedCache k i : ℝ) / (64 * Real.sqrt 2)

private theorem canonical_incoming_C
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    generatedTenthSourceCompactIncomingPacket.2.1 r =
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r : ℝ) / 16 := by
  rw [generatedTenth_source_compact_incoming_short]
  exact generatedTenth_final_short_source_incoming_C hin r

private theorem canonical_incoming_T
    (hB : GeneratedTenthSourceCompactCanonicalBCondition) (t : SpinIndex) (i : Fin 24) :
    generatedTenthSourceCompactIncomingPacket.2.2 t i =
      (((generatedTenthIncomingTensorPackedCache (nortonUIntegerLabel t) i : ℚ) / 64 : ℚ) :
        ℝ) / Real.sqrt 2 := by
  have h := hB (nortonUIntegerLabel t) i
  simpa only [nortonUIntegerLabel_inverse, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_ofNat, div_div] using h

private theorem canonical_C_formula (r : GriessShortIndex) :
    generatedTenthFinalShortSourceGenericFormula generatedTenthSourceIncomingMatrixLiteral
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
      (fun k i => (generatedTenthIncomingTensorPackedCache k i : ℚ) / 64) r =
        (generatedTenthFinalSourceCertificateCInteger r : ℚ) := by
  rw [← generatedTenth_final_source_certificate_C_rational]
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · rfl
  · simp only [generatedTenthFinalShortSourceGenericFormula,
      generatedTenthFinalShortSourceCalibratedFormula]
    ring

/-- Every canonical final C128 coefficient uses the entire genuine triality formula. -/
theorem generatedTenth_source_compact_canonical_final_C_integer
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (hB : GeneratedTenthSourceCompactCanonicalBCondition) (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthSourceCompactAxis).2.1 r =
      (generatedTenthFinalSourceCertificateCInteger r : ℝ) := by
  have hm : ∀ i j, generatedTenthSourceCompactIncomingPacket.1 i j =
      (generatedTenthSourceIncomingMatrixLiteral i j : ℝ) := by
    intro i j
    rw [generatedTenth_source_compact_incoming_matrix]
    exact generatedTenth_source_incoming_matrix_literal_actual i j
  have ht : ∀ k i,
      generatedTenthSourceCompactIncomingPacket.2.2 (golayLabelCoefficients k) i =
        (((generatedTenthIncomingTensorPackedCache k i : ℚ) / 64 : ℚ) : ℝ) /
          Real.sqrt 2 := by
    intro k i
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, div_div] using hB k i
  rw [generatedTenth_source_compact_final_packet_actual]
  change 128 * generatedAxisGlobalRawTrialityShort
    generatedTenthSourceCompactIncomingPacket r = _
  rw [generatedTenth_final_short_source_generic_actual _ _ _ _ hm
    (canonical_incoming_C hin) ht r, canonical_C_formula]
  simp only [Rat.cast_intCast]

private theorem canonical_T_formula (k : Fin 4096) (i : Fin 24) :
    512 * generatedAxisGlobalTrialityScaledTensorQ
      generatedTenthFinalTensorSourceIncomingCQ
      (fun t j => (generatedTenthIncomingTensorPackedCache (nortonUIntegerLabel t) j : ℚ) / 64)
      (golayLabelCoefficients k) i =
        (generatedTenthFinalSourceCertificateTInteger k i : ℚ) := by
  unfold generatedAxisGlobalTrialityScaledTensorQ generatedTenthFinalTensorSourceIncomingCQ
    generatedTenthFinalSourceCertificateTInteger
  simp only [generatedAxisGlobalSpinLabel_coeff, nortonUIntegerLabel_coeff]
  rw [generatedTenth_final_source_certificate_incoming_actual]
  push_cast
  split_ifs <;> ring

/-- Every final tensor numerator retains both incoming C and incoming tensor difference. -/
theorem generatedTenth_source_compact_canonical_final_T_integer
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (hB : GeneratedTenthSourceCompactCanonicalBCondition) (k : Fin 4096) (i : Fin 24) :
    512 * Real.sqrt 2 * (griessConwayEncode generatedTenthSourceCompactAxis).2.2
      (golayLabelCoefficients k) i = (generatedTenthFinalSourceCertificateTInteger k i : ℝ) := by
  let x := rhoLocal (localFiberIntoH generatedTenthSourceCompactFiber) generatedFifthAxis
  have hc : ∀ r, (griessConwayEncode x).2.1 r =
      (generatedTenthFinalTensorSourceIncomingCQ r : ℝ) := by
    intro r
    simpa only [x, generatedTenthSourceCompactIncomingPacket,
      generatedTenthFinalTensorSourceIncomingCQ, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_ofNat] using canonical_incoming_C hin r
  have ht : ∀ t j, (griessConwayEncode x).2.2 t j =
      (((generatedTenthIncomingTensorPackedCache (nortonUIntegerLabel t) j : ℚ) / 64 : ℚ) :
        ℝ) / Real.sqrt 2 := by
    intro t j
    exact canonical_incoming_T hB t j
  have h := generatedAxisGlobalTrialityScaledTensorQ_actual x _ _ hc ht
    (golayLabelCoefficients k) i
  rw [generatedTenth_source_compact_axis_expression]
  change 512 * Real.sqrt 2 * (griessConwayEncode (sExtra x)).2.2 _ i = _
  rw [h]
  have hf := congrArg (fun q : ℚ => (q : ℝ)) (canonical_T_formula k i)
  push_cast at hf
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  calc
    _ = 512 * (generatedAxisGlobalTrialityScaledTensorQ
        generatedTenthFinalTensorSourceIncomingCQ
        (fun t j => (generatedTenthIncomingTensorPackedCache (nortonUIntegerLabel t) j : ℚ) /
          64) (golayLabelCoefficients k) i : ℝ) := by field_simp [hn]
    _ = _ := hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
