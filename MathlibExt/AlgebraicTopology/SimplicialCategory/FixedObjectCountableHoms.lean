/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialQuiverCountability
import MathlibExt.AlgebraicTopology.SimplicialSet.CountableSimplicesColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimits

/-!
# Countability of the entire original fixed-label Hom colimits

Every original label Hom retains countability in all original degrees.
Whole original isomorphisms preserve this property. Actual fixed-label
diagram colimits are quotients of free paths on the countable family
of original stage Hom generators. Arbitrarily many actual relations do
not add generators. Thus countable original labels and stage objects
give countable entire original colimit Homs.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- Every whole original fixed-label Hom has its actual countable simplices in each degree. -/
class CountableHoms (C : FixedObjects O) : Prop where
  countable_hom (x y : O) : (hom C x y).CountableSimplices

attribute [instance] CountableHoms.countable_hom

/-- Countability retains every original object, with only its proved whole Hom-label isomorphism. -/
theorem countable_originalHom (C : FixedObjects O) [CountableHoms C] (a b : C.val) :
    (a ⟶[SSet.{u}] b).CountableSimplices :=
  SSet.countableSimplices_of_iso (originalHomIso C a b)

/-- The SAME entire original fixed-label isomorphism preserves countability at every original ordered pair. -/
theorem countableHoms_of_iso {C D : FixedObjects O} (e : C ≅ D) [CountableHoms D] : CountableHoms C where
  countable_hom x y := by
    have : ((evaluation x y).obj D).CountableSimplices := CountableHoms.countable_hom (C := D) x y
    exact SSet.countableSimplices_of_iso ((evaluation x y).mapIso e)

variable [Countable O]

/-- Actual full presented Homs remain countable on the SAME original labels and generators. -/
instance presentations_countable (Q : SimplicialQuiver.Data O)
    [∀ x y, (Q.Hom x y).CountableSimplices] (R : SimplicialQuiver.Relations Q) :
    CountableHoms (Presentations.object Q R) where
  countable_hom x y := SimplicialQuiver.presentedHom_countableSimplices Q R x y

variable {J : Type v} [Category.{w} J] [Small.{u} J] [Countable J]

/-- Every original diagram-generator Hom is the countable coproduct of the SAME actual original stage Homs. -/
instance diagramGenerator_countable (F : J ⥤ FixedObjects O) [∀ j, CountableHoms (F.obj j)] (x y : O) :
    ((DiagramPresentation.quiver F).Hom x y).CountableSimplices := by
  have (j : J) : (hom (F.obj j) x y).CountableSimplices := inferInstance
  exact SSet.countableSimplices_coproduct (fun j => hom (F.obj j) x y)

/-- The actual full original fixed-label colimit presentation has countable entire Homs. -/
instance diagramPresentation_countable (F : J ⥤ FixedObjects O) [∀ j, CountableHoms (F.obj j)] :
    CountableHoms (DiagramPresentation.object F) :=
  presentations_countable (DiagramPresentation.quiver F) (DiagramPresentation.relations F)

/-- The genuine chosen colimit of the SAME whole original countable diagram has countable full Homs. -/
instance colimit_countable (F : J ⥤ FixedObjects O) [HasColimit F] [∀ j, CountableHoms (F.obj j)] :
    CountableHoms (colimit F) := by
  have : CountableHoms (DiagramPresentation.cocone F).pt := diagramPresentation_countable F
  exact countableHoms_of_iso
    ((colimit.isColimit F).coconePointUniqueUpToIso (DiagramPresentation.isColimit F))

end CategoryTheory.SimplicialEnrichment.FixedObjects
