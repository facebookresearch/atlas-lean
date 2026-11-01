/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairWitness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates

/-! The actual middle vector has only three possible pair-short rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Outside the pair family, every original third-axis short coefficient is zero. -/
theorem generatedSixth_original_nonpair_zero (r : GriessShortIndex)
    (hr : ∀ s p, r ≠ Sum.inl (s, p)) :
    (griessConwayEncode generatedOddAxis).2.1 r = 0 := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, i⟩
  · exact (hr s p rfl).elim
  · exact generatedAxis_triality_odd_octad_coordinate 0 0 0 o e
  · exact generatedAxis_triality_odd_odd_coordinate 0 d 0 i 0

/-- Every one of the 549 excluded actual pair rows vanishes in the original local image. -/
theorem generatedSixth_middle_pair_zero (s : Fin 2) (p : Fin 276)
    (hp : ¬ generatedSixthPairExceptional s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (s, p)) = 0 := by
  rw [generatedFourth_local_short]
  let r := griessShortPermutation (generatedSixthLocalFiber.val.2⁻¹) (Sum.inl (s, p))
  have hr := generatedSixth_pair_inverse_not_pair s p hp
  have hz : (griessConwayEncode generatedOddAxis).2.1 r = 0 :=
    generatedSixth_original_nonpair_zero r hr
  have hi : griessShortPermutation generatedSixthLocalFiber.val.2 r = Sum.inl (s, p) := by
    change (griessShortPermutation generatedSixthLocalFiber.val.2)
      ((griessShortPermutation (generatedSixthLocalFiber.val.2⁻¹)) (Sum.inl (s, p))) = _
    rw [map_inv]
    exact Equiv.apply_symm_apply _ _
  rw [← hi, localShortOperator_image, hz, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
