/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort3Phase

/-! Bounded original physical transport and full signed coefficients for seven octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Seven consecutive actual outgoing octad families. -/
def generatedFifthPermutationShort3Packet0Family (j : Fin 7) : Fin 56 := ⟨0 + j.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check literal physical coordinates and the original signed coefficient for these seven families.
/-- Actual inverse transport and complete coefficient equality for each preferred short target. -/
theorem generatedFifth_permutation_short3_packet0_certificate : ∀ j : Fin 7, ∀ e : Fin 64,
    (generatedFifthPermutationShort3PhysicalSign
        (generatedFifthPermutationShort3Packet0Family j) e = 1 ∨
      generatedFifthPermutationShort3PhysicalSign
        (generatedFifthPermutationShort3Packet0Family j) e = -1) ∧
    (∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral (generatedFifthPermutationShort3OctadSource
        (generatedFifthPermutationShort3Packet0Family j) e)
        (generatedFifthPermutationShort3Inverse i) =
      generatedFifthPermutationShort3PhysicalSign
        (generatedFifthPermutationShort3Packet0Family j) e *
        generatedFifthXiShortCachedIntegral
          (Sum.inr (generatedFifthPermutationShort3Packet0Family j, e)) i) ∧
    nortonUIntegerSign (generatedFifthPermutationShort3Phase
        (generatedFifthPermutationShort3Packet0Family j) e) *
      generatedFifthXiShortCachedNumerator (generatedFifthPermutationShort3OctadSource
        (generatedFifthPermutationShort3Packet0Family j) e) =
        generatedFifthXiShortCachedNumerator
          (Sum.inr (generatedFifthPermutationShort3Packet0Family j, e)) := by
  decide +kernel

/-- A checked packet fixes all its genuine outgoing short-coordinate rows. -/
theorem generatedFifth_permutation_short3_packet0_coordinate
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 3))
    (j : Fin 7) (e : Fin 64) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 3)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven
            (Sum.inr (generatedFifthPermutationShort3Packet0Family j, e)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven
            (Sum.inr (generatedFifthPermutationShort3Packet0Family j, e)))) := by
  rcases generatedFifth_permutation_short3_packet0_certificate j e with ⟨hs, hv, hn⟩
  apply generatedFifth_monomial_permutation_short_coordinate 3 hp
    (generatedFifthPermutationShort3OctadSource
        (generatedFifthPermutationShort3Packet0Family j) e) _
  · apply generatedFifth_monomial_permutation_physical_sign 3 _ _ _ hs
    intro i
    rw [generatedFifth_permutation_short3_inverse]
    exact hv i
  · rw [generatedFifth_permutation_short3_actual_phase]
    exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
