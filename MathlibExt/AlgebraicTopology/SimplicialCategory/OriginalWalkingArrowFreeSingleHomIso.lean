/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeSingleHomCofibrant
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback

/-!
# The SAME original two-label free arrow and walking arrow

The original free single-Hom object at the two distinct walking labels
has its genuine full generator evaluation to the original walking arrow.
The existing walking-arrow representation constructs its inverse. Both
whole inverse equations retain every original object, identity, forward
coefficient, empty reverse Hom and full original finite path.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowFreeSingleHomIso
open FixedObjects

/-- The SAME original walking arrow supplies its two original object labels. -/
abbrev walking : Carrier.{u} := BergnerTwoObject.object (𝟙_ SSet.{u})

/-- The full original walking arrow placed over its SAME original labels. -/
abbrev walkingFixed : FixedObjects walking.{u} := ⟨walking, rfl⟩

/-- The original free unit-Hom arrow on those SAME two distinct labels. -/
abbrev free : FixedObjects walking.{u} :=
  FreeSingleHom.object (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u})

/-- Evaluate every original free path in the SAME original walking arrow. -/
def toWalking : free.{u} ⟶ walkingFixed :=
  FreeSingleHom.extend _ _ (𝟙_ SSet.{u}) walkingFixed (𝟙 _)

/-- The existing walking-arrow representation reads the SAME original free generator. -/
def fromWalking : walkingFixed.{u} ⟶ free := by
  let F := BergnerTwoObject.ofMap
    (vertex free (BergnerTwoObject.source (𝟙_ SSet.{u})))
    (vertex free (BergnerTwoObject.target (𝟙_ SSet.{u})))
    (FreeSingleHom.generator _ _ (𝟙_ SSet.{u}))
  exact CarrierLabelReadback.map walkingFixed (vertex free) F (fun x => by
    cases x with | up x => cases x <;> rfl)

/-- Both full original functors recover every original free path and object. -/
theorem toWalking_fromWalking : toWalking.{u} ≫ fromWalking = 𝟙 free := by
  apply (FreeSingleHom.homEquiv _ _ (𝟙_ SSet.{u}) free).injective
  change FreeSingleHom.restrict _ _ (𝟙_ SSet.{u}) free (toWalking ≫ fromWalking) =
    FreeSingleHom.restrict _ _ (𝟙_ SSet.{u}) free (𝟙 free)
  have hc := FreeSingleHom.restrict_comp _ _ (𝟙_ SSet.{u}) toWalking fromWalking
  have hto := FreeSingleHom.restrict_extend
    (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) walkingFixed
    (𝟙 (𝟙_ SSet.{u}))
  change FreeSingleHom.restrict _ _ (𝟙_ SSet.{u}) walkingFixed toWalking = 𝟙 _ at hto
  have hfrom : homMap fromWalking (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) = FreeSingleHom.generator _ _ _ := by
    rfl
  exact hc.trans ((congrArg (fun f => f ≫ homMap fromWalking _ _) hto).trans
    ((Category.id_comp _).trans (hfrom.trans (Category.comp_id _).symm)))

/-- Both full original functors recover the SAME actual walking arrow with all coefficient maps. -/
theorem fromWalking_toWalking : fromWalking.{u} ≫ toWalking = 𝟙 walkingFixed := by
  apply Functor.Fiber.hom_ext
  apply (BergnerTwoObject.functorEquiv).injective
  change (⟨_, ⟨_, _⟩⟩ : Σ x : walking.{u}, Σ y : walking.{u},
    (𝟙_ SSet.{u}) ⟶ x ⟶[SSet.{u}] y) = ⟨_, ⟨_, _⟩⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Sigma.ext rfl
  apply heq_of_eq
  change FreeSingleHom.generator _ _ (𝟙_ SSet.{u}) ≫ homMap toWalking _ _ = 𝟙 _
  exact FreeSingleHom.restrict_extend
    (BergnerTwoObject.source (𝟙_ SSet.{u}))
    (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) walkingFixed
    (𝟙 (𝟙_ SSet.{u}))

/-- The full actual original two-label walking arrow is the SAME free single-Hom source. -/
def iso : free.{u} ≅ walkingFixed where
  hom := toWalking
  inv := fromWalking
  hom_inv_id := toWalking_fromWalking
  inv_hom_id := fromWalking_toWalking

end CategoryTheory.SimplicialEnrichment.OriginalWalkingArrowFreeSingleHomIso
