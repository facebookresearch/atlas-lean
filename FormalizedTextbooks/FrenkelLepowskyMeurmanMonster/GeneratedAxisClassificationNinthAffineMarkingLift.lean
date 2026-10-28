/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCo1Projection

/-! The actual binary marking condition pulls back to the whole lattice-quotient carrier. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Conway lift of a marking stabilizer preserves the actual class carrier. -/
theorem generatedNinth_affine_marking_lift_preserved (g : leechIsomSubgroup)
    (hg : QuotientGroup.mk' signsSubgroup g ∈ generatedNinthCo1MarkingStabilizer) :
    leechModTwoAction g '' generatedNinthMarkedShortClasses =
      generatedNinthMarkedShortClasses := by
  change leechBinaryAction g ''
    (leechHyperbolicCoordinates '' generatedNinthMarkedShortClasses) =
      leechHyperbolicCoordinates '' generatedNinthMarkedShortClasses at hg
  apply (Set.image_injective.mpr leechHyperbolicCoordinates.injective)
  calc
    leechHyperbolicCoordinates ''
        (leechModTwoAction g '' generatedNinthMarkedShortClasses) =
      leechBinaryAction g ''
        (leechHyperbolicCoordinates '' generatedNinthMarkedShortClasses) := by
      rw [Set.image_image, Set.image_image]
      apply congrArg (fun f => f '' generatedNinthMarkedShortClasses)
      funext v
      exact (leechBinaryAction_coordinates g v).symm
    _ = leechHyperbolicCoordinates '' generatedNinthMarkedShortClasses := hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
