/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort1Pairs

/-! Bounded original pair transport and complete signed coefficients for two first coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two consecutive first coordinates of genuine ordered physical pairs. -/
def generatedFifthPermutationShort1PairPacket3First (a : Fin 2) : Fin 24 := ⟨6 + a.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check bounded literal pairs with their preferred vector sign and original coefficient.
/-- Every pair in this packet has exact inverse transport and signed coefficient equality. -/
theorem generatedFifth_permutation_short1_pair_packet3_certificate :
    ∀ s : Fin 2, ∀ a : Fin 2, ∀ b : Fin 24,
    ∀ h : generatedFifthPermutationShort1PairPacket3First a < b,
    let p : {p : Fin 24 × Fin 24 // p.1 < p.2} :=
      ⟨(generatedFifthPermutationShort1PairPacket3First a, b), h⟩
    (generatedFifthPermutationShort1PairPhysicalSign s p = 1 ∨
      generatedFifthPermutationShort1PairPhysicalSign s p = -1) ∧
    (∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral (generatedFifthPermutationShort1PairSource s p)
        (generatedFifthPermutationShort1Inverse i) =
      generatedFifthPermutationShort1PairPhysicalSign s p *
        generatedFifthXiShortCachedIntegral (Sum.inl (s, p)) i) ∧
    nortonUIntegerSign (generatedFifthPermutationPairPhase 1 p.val.1 p.val.2) *
      generatedFifthXiShortCachedNumerator (generatedFifthPermutationShort1PairSource s p) =
        generatedFifthXiShortCachedNumerator (Sum.inl (s, p)) := by
  decide +kernel

/-- Exact finite transport and original coefficients fix each actual pair in this packet. -/
theorem generatedFifth_permutation_short1_pair_packet3_coordinate
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 1))
    (s a : Fin 2) (b : Fin 24) (h : generatedFifthPermutationShort1PairPacket3First a < b) :
    let p : {p : Fin 24 × Fin 24 // p.1 < p.2} :=
      ⟨(generatedFifthPermutationShort1PairPacket3First a, b), h⟩
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 1)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) := by
  rcases generatedFifth_permutation_short1_pair_packet3_certificate s a b h with
    ⟨hs, hv, hn⟩
  apply generatedFifth_monomial_permutation_short_coordinate 1 hp
    (generatedFifthPermutationShort1PairSource s
      ⟨(generatedFifthPermutationShort1PairPacket3First a, b), h⟩) _
  · apply generatedFifth_monomial_permutation_physical_sign 1 _ _ _ hs
    intro i
    rw [generatedFifth_permutation_short1_inverse]
    exact hv i
  · rw [generatedFifth_permutation_pair_phase]
    exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
