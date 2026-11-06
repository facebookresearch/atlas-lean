/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort0Phase

/-! Bounded original physical transport and full signed coefficients for seven octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Seven consecutive actual outgoing octad families. -/
def generatedFifthPermutationShort0Packet4Family (j : Fin 7) : Fin 56 := ⟨28 + j.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check literal physical coordinates and the original signed coefficient for these seven families.
/-- Actual inverse transport and complete coefficient equality for each preferred short target. -/
theorem generatedFifth_permutation_short0_packet4_certificate : ∀ j : Fin 7, ∀ e : Fin 64,
    (generatedFifthPermutationShort0PhysicalSign
        (generatedFifthPermutationShort0Packet4Family j) e = 1 ∨
      generatedFifthPermutationShort0PhysicalSign
        (generatedFifthPermutationShort0Packet4Family j) e = -1) ∧
    (∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral (generatedFifthPermutationShort0OctadSource
        (generatedFifthPermutationShort0Packet4Family j) e)
        (generatedFifthPermutationShort0Inverse i) =
      generatedFifthPermutationShort0PhysicalSign
        (generatedFifthPermutationShort0Packet4Family j) e *
        generatedFifthXiShortCachedIntegral
          (Sum.inr (generatedFifthPermutationShort0Packet4Family j, e)) i) ∧
    nortonUIntegerSign (generatedFifthPermutationShort0Phase
        (generatedFifthPermutationShort0Packet4Family j) e) *
      generatedFifthXiShortCachedNumerator (generatedFifthPermutationShort0OctadSource
        (generatedFifthPermutationShort0Packet4Family j) e) =
        generatedFifthXiShortCachedNumerator
          (Sum.inr (generatedFifthPermutationShort0Packet4Family j, e)) := by
  decide +kernel

/-- A checked packet fixes all its genuine outgoing short-coordinate rows. -/
theorem generatedFifth_permutation_short0_packet4_coordinate
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 0))
    (j : Fin 7) (e : Fin 64) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 0)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven
            (Sum.inr (generatedFifthPermutationShort0Packet4Family j, e)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven
            (Sum.inr (generatedFifthPermutationShort0Packet4Family j, e)))) := by
  rcases generatedFifth_permutation_short0_packet4_certificate j e with ⟨hs, hv, hn⟩
  apply generatedFifth_monomial_permutation_short_coordinate 0 hp
    (generatedFifthPermutationShort0OctadSource
        (generatedFifthPermutationShort0Packet4Family j) e) _
  · apply generatedFifth_monomial_permutation_physical_sign 0 _ _ _ hs
    intro i
    rw [generatedFifth_permutation_short0_inverse]
    exact hv i
  · rw [generatedFifth_permutation_short0_actual_phase]
    exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
