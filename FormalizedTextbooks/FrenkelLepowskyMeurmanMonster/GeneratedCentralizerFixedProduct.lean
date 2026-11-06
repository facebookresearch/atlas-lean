/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual fixed eigenspace algebra and its centralizer automorphisms. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual fixed eigenspace is closed under the original Griess product. -/
theorem generatedCentralPlus_mul_plus (x y : GriessSpace)
    (hx : x ∈ generatedCentralPlus) (hy : y ∈ generatedCentralPlus) :
    griessProd x y ∈ generatedCentralPlus := by
  rw [mem_generatedCentralPlus] at hx hy ⊢
  have hz := rhoLocal_product (inclQ qCentralInvolution) x y
  change localCentralGriess (griessProd x y) =
    griessProd (localCentralGriess x) (localCentralGriess y) at hz
  rw [hz, hx, hy]

/-- The fixed-space product is the restriction of the actual algebra product. -/
noncomputable def generatedCentralPlusProduct (x y : generatedCentralPlus) :
    generatedCentralPlus :=
  ⟨griessProd x.val y.val, generatedCentralPlus_mul_plus x.val y.val x.property y.property⟩

/-- Restricting the actual centralizer preserves the restricted actual product. -/
theorem generatedCentralPlusProduct_covariant (g : generatedCentralizer)
    (x y : generatedCentralPlus) :
    generatedCentralizerPlusEquiv g (generatedCentralPlusProduct x y) =
      generatedCentralPlusProduct (generatedCentralizerPlusEquiv g x)
        (generatedCentralizerPlusEquiv g y) := by
  apply Subtype.ext
  exact generated_group_preserves_griessProduct sExtra_preserves_griessProd g.val x.val y.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
