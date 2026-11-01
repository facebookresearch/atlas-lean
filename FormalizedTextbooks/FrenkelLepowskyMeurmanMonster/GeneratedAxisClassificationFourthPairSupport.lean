/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairCoordinates

/-! Exact original pair-coordinate support in the literal fourth candidate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual pair row of the local transition, including its preferred phase. -/
theorem generatedFourth_transported_pair_coordinate (s : Fin 2) (p : Fin 276) :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inl (s, p)) =
      if s = 1 ∧ griessCoordinatePair p = (8, 11) then
        -qSign generatedFourthPairPhase else 0 := by
  by_cases h : s = 1 ∧ griessCoordinatePair p = (8, 11)
  · rw [ite_eq_left h]
    obtain ⟨rfl, hp⟩ := h
    have he : p = griessPairIndex 8 11 (by decide) := by
      apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      change griessCoordinatePair p = griessCoordinatePair (griessPairIndex 8 11 (by decide))
      exact hp.trans generatedFourthPairInput_coordinates.symm
    subst p
    exact generatedFourth_transported_pair_input
  · rw [ite_eq_right h]
    by_contra hn
    have hs := (generatedFourth_transported_short_support generatedFourthLocalFiber
      generatedFourthOctad 0 0 (Sum.inl (s, p))).mp hn
    rw [generatedFourthOctad_mask] at hs
    exact h ((generatedFourth_inverse_pair_support s p).mp hs)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
