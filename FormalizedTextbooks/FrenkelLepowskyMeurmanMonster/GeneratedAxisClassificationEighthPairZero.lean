/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthPairWitness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairZero

/-! All original middle signed-pair coordinates vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual pair row vanishes in the original local image. -/
theorem generatedEighth_middle_pair_zero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
        (Sum.inl (s, p)) = 0 := by
  rw [generatedFourth_local_short]
  let r := griessShortPermutation (generatedEighthLocalFiber.val.2⁻¹) (Sum.inl (s, p))
  have hr := generatedEighth_pair_inverse_not_pair s p
  have hz : (griessConwayEncode generatedOddAxis).2.1 r = 0 :=
    generatedSixth_original_nonpair_zero r hr
  have hi : griessShortPermutation generatedEighthLocalFiber.val.2 r = Sum.inl (s, p) := by
    change (griessShortPermutation generatedEighthLocalFiber.val.2)
      ((griessShortPermutation (generatedEighthLocalFiber.val.2⁻¹)) (Sum.inl (s, p))) = _
    rw [map_inv]
    exact Equiv.apply_symm_apply _ _
  rw [← hi, localShortOperator_image, hz, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
