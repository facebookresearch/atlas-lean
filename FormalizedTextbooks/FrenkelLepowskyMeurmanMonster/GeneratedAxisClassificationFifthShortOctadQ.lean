/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQCandidate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! Actual binary conjugation characters on all pair and outgoing octad short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- The all-one spin coordinate tests the last modulation bit. -/
theorem generatedFifth_spin_dot_omega_left (b : ZMod 2) (v : SpinIndex) :
    spinDot (b • (Pi.single 11 1 : SpinIndex)) v = b * v 11 := by
  simp [spinDot, Pi.smul_apply, Pi.single_apply, ite_mul, mul_ite]

/-- Modulation pairing with a scalar all-one coordinate tests the same last bit. -/
theorem generatedFifth_spin_dot_omega_right (b : ZMod 2) (v : SpinIndex) :
    spinDot v (b • (Pi.single 11 1 : SpinIndex)) = v 11 * b := by
  simp [spinDot, Pi.smul_apply, Pi.single_apply, mul_ite]

/-- Every allowed modulation has zero all-one coefficient. -/
theorem generatedFifth_modulation_last (k : Fin 16) :
    golayLabelCoefficients (generatedFifthModulationLabels k) 11 = 0 :=
  ((generatedFifth_modulation_certificate (generatedFifthModulationLabels k)).mpr
    ⟨k, rfl⟩).1

set_option maxHeartbeats 2000000 in
-- Check 16 modulation characters against the 56 actual original Golay family labels.
/-- Every allowed modulation annihilates each outgoing octad's actual code coordinates. -/
theorem generatedFifth_short_octad_code_certificate : ∀ k : Fin 16, ∀ j : Fin 56,
    spinDot (golayLabelCoefficients (generatedFifthModulationLabels k))
      (golayLabelCoefficients (generatedFifthEvenRootCode j)) = 0 := by
  decide +kernel

/-- Every actual tensor candidate fixes the conjugation phase of all pair-short coordinates. -/
theorem generatedFifth_candidate_pair_Q_phase (b : ZMod 2) (k : Fin 16)
    (s : Fin 2) (p : Fin 276) :
    localAxisQPhase (Sum.inl (s, p)) (generatedFifthQCandidate b k) = 1 := by
  apply (generatedFourthQShortBasis_character_one_iff _ _).mpr
  rw [generatedFifthQCandidate, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation, griessPairQ_modulation,
    griessPairQ_translation, generatedFifth_spin_dot_omega_left, griessPairSyndrome_omega]
  by_cases hs : s = 0
  · simp [hs]
  · have ho : spinDot (golayLabelCoefficients (generatedFifthModulationLabels k))
        (Pi.single 11 1) = 0 := by
      simpa only [one_smul, generatedFifth_modulation_last, zero_mul] using
        generatedFifth_spin_dot_omega_right 1
          (golayLabelCoefficients (generatedFifthModulationLabels k))
    simp only [hs, ite_false, ho, mul_zero, zero_add]

/-- Every actual tensor candidate fixes all 64 preferred sign rows of each outgoing octad. -/
theorem generatedFifth_candidate_octad_Q_phase (b : ZMod 2) (k : Fin 16)
    (j : Fin 56) (e : Fin 64) :
    localAxisQPhase (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e)))
      (generatedFifthQCandidate b k) = 1 := by
  apply (generatedFourthQShortBasis_character_one_iff _ _).mpr
  rw [generatedFifthQCandidate, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation, generatedFifth_spin_dot_omega_left,
    griessOctad_modulation_last, griessOctad_translation, spinDot_add_right,
    generatedFifthEvenRootOctad_label, generatedFifth_short_octad_code_certificate,
    generatedFifth_spin_dot_omega_right, generatedFifth_modulation_last]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
