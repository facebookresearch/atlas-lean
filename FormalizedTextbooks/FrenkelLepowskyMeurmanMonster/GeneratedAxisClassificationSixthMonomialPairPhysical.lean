/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairSource

/-! Actual original monomial action identifies every preferred source and target pair line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine source pair is carried to its actual target vector up to global sign. -/
theorem generatedSixth_monomial_pair_source_vector (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2.val
      (griessShortVector (Sum.inl (s, generatedSixthMonomialPairSourceIndex k p))) =
        griessShortVector (Sum.inl (s, p)) ∨
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2.val
      (griessShortVector (Sum.inl (s, generatedSixthMonomialPairSourceIndex k p))) =
        -griessShortVector (Sum.inl (s, p)) := by
  have hc := generatedSixth_monomial_pair_source_coordinates k p
  have h₁ (i : Fin 24) : generatedSixthMonomialPairInput k i =
      generatedSixthMonomialPairInput k (griessCoordinatePair p).1 ↔
        i = (griessCoordinatePair p).1 :=
    (generatedSixth_monomial_pair_input_injective k).eq_iff
  have h₂ (i : Fin 24) : generatedSixthMonomialPairInput k i =
      generatedSixthMonomialPairInput k (griessCoordinatePair p).2 ↔
        i = (griessCoordinatePair p).2 :=
    (generatedSixth_monomial_pair_input_injective k).eq_iff
  by_cases h : generatedSixthMonomialPairInput k (griessCoordinatePair p).1 <
      generatedSixthMonomialPairInput k (griessCoordinatePair p).2
  · left
    funext i
    rw [generatedSixth_monomial_physical_apply]
    change griessShortVector _ (generatedSixthMonomialPairInput k i) = _
    simp only [griessShortVector, griessShortIntegral, hc, h, ite_true,
      h₁ i, h₂ i]
  · by_cases hs : s = 0
    · right
      funext i
      rw [generatedSixth_monomial_physical_apply]
      change griessShortVector _ (generatedSixthMonomialPairInput k i) = _
      simp only [griessShortVector, griessShortIntegral, hc, h, ite_false, hs, ite_true,
        h₁ i, h₂ i, Pi.neg_apply]
      push_cast
      ring
    · left
      funext i
      rw [generatedSixth_monomial_physical_apply]
      change griessShortVector _ (generatedSixthMonomialPairInput k i) = _
      simp only [griessShortVector, griessShortIntegral, hc, h, ite_false, hs, h₁ i, h₂ i]
      push_cast
      ring

/-- The actual preferred-label permutation is identified without dropping any Q phase. -/
theorem generatedSixth_monomial_pair_source_permutation (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inl (s, generatedSixthMonomialPairSourceIndex k p)) = Sum.inl (s, p) := by
  apply generatedSixth_short_permutation_of_vector
  exact generatedSixth_monomial_pair_source_vector k s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
