/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQPhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! Literal actual Pauli candidates fixing the full original fifth tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Q elements with the verified translation, modulation, and central phase. -/
def generatedFifthQCandidate (b : ZMod 2) (k : Fin 16) : Q :=
  generatedAxisFourthQFromSpin (b • (Pi.single 11 1 : SpinIndex))
    (golayLabelCoefficients (generatedFifthModulationLabels k))
    (spinDot (golayLabelCoefficients (generatedFifthModulationLabels k))
      (generatedFifthSpinLow (generatedFifthColumnLabels 0)) + b)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the bounded actual binary dictionary and phase certificate.
/-- Every candidate has exactly the fixing phase at both actual spin indices of all 64 rows. -/
theorem generatedFifth_candidate_phase_certificate : ∀ b : ZMod 2, ∀ k : Fin 16,
    ∀ j : Fin 64, ∀ h : ZMod 2,
      spinPhase (generatedFifthQCandidate b k)
        (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
          h • (Pi.single 11 1 : SpinIndex)) + b = 0 := by
  decide +kernel

/-- Each candidate acts on every original tensor column by its exact signed translation. -/
theorem generatedFifth_candidate_translation (b : ZMod 2) (k : Fin 16)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.2
        (t + spinTranslation (generatedFifthQCandidate b k)) i =
      qSign b * (griessConwayEncode generatedFifthAxis).2.2 t i := by
  rw [generatedFifthQCandidate, generatedAxisFourthQFromSpin_translation]
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · simp only [zero_smul, add_zero, qSign_zero, one_mul]
  · simp only [one_smul, generatedFifth_tensor_add_omega, qSign_one, neg_one_mul]

/-- All 32 literal candidates genuinely fix every original tensor coordinate. -/
theorem generatedFifth_candidate_tensor_fixed (b : ZMod 2) (k : Fin 16) (i : Fin 24) :
    spinRepresentation (generatedFifthQCandidate b k)
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
        (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) := by
  apply funext
  intro t
  change qSign (spinPhase (generatedFifthQCandidate b k) t) *
    (griessConwayEncode generatedFifthAxis).2.2
      (t + spinTranslation (generatedFifthQCandidate b k)) i = _
  rw [generatedFifth_candidate_translation, ← mul_assoc, ← qSign_add]
  by_cases ht : (griessConwayEncode generatedFifthAxis).2.2 t i = 0
  · rw [ht, mul_zero]
  · obtain ⟨j, hj⟩ := (generatedFifth_tensor_nonzero_iff t i).mp ht
    obtain ⟨h, hh⟩ := generatedFifth_spin_dictionary_decomposition t
    have hd : (generatedFifthOddRootOutputData j).1 = spinDictionaryCode t :=
      congrArg Prod.fst hj
    have he := generatedFifth_candidate_phase_certificate b k j h
    rw [hd, ← hh] at he
    rw [he, qSign_zero, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
