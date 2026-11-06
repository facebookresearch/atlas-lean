/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort5Pairs

/-! Bounded original pair transport and complete signed coefficients for two first coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two consecutive first coordinates of genuine ordered physical pairs. -/
def generatedFifthPermutationShort5PairPacket10First (a : Fin 2) : Fin 24 := ⟨20 + a.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check bounded literal pairs with their preferred vector sign and original coefficient.
/-- Every pair in this packet has exact inverse transport and signed coefficient equality. -/
theorem generatedFifth_permutation_short5_pair_packet10_certificate :
    ∀ s : Fin 2, ∀ a : Fin 2, ∀ b : Fin 24,
    ∀ h : generatedFifthPermutationShort5PairPacket10First a < b,
    let p : {p : Fin 24 × Fin 24 // p.1 < p.2} :=
      ⟨(generatedFifthPermutationShort5PairPacket10First a, b), h⟩
    (generatedFifthPermutationShort5PairPhysicalSign s p = 1 ∨
      generatedFifthPermutationShort5PairPhysicalSign s p = -1) ∧
    (∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral (generatedFifthPermutationShort5PairSource s p)
        (generatedFifthPermutationShort5Inverse i) =
      generatedFifthPermutationShort5PairPhysicalSign s p *
        generatedFifthXiShortCachedIntegral (Sum.inl (s, p)) i) ∧
    nortonUIntegerSign (generatedFifthPermutationPairPhase 5 p.val.1 p.val.2) *
      generatedFifthXiShortCachedNumerator (generatedFifthPermutationShort5PairSource s p) =
        generatedFifthXiShortCachedNumerator (Sum.inl (s, p)) := by
  decide +kernel

/-- Exact finite transport and original coefficients fix each actual pair in this packet. -/
theorem generatedFifth_permutation_short5_pair_packet10_coordinate
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 5))
    (s a : Fin 2) (b : Fin 24) (h : generatedFifthPermutationShort5PairPacket10First a < b) :
    let p : {p : Fin 24 × Fin 24 // p.1 < p.2} :=
      ⟨(generatedFifthPermutationShort5PairPacket10First a, b), h⟩
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 5)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) := by
  rcases generatedFifth_permutation_short5_pair_packet10_certificate s a b h with
    ⟨hs, hv, hn⟩
  apply generatedFifth_monomial_permutation_short_coordinate 5 hp
    (generatedFifthPermutationShort5PairSource s
      ⟨(generatedFifthPermutationShort5PairPacket10First a, b), h⟩) _
  · apply generatedFifth_monomial_permutation_physical_sign 5 _ _ _ hs
    intro i
    rw [generatedFifth_permutation_short5_inverse]
    exact hv i
  · rw [generatedFifth_permutation_pair_phase]
    exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
