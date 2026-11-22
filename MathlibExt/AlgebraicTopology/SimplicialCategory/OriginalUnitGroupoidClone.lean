/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexing
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanTwoOutOfThree

/-!
# The literal original unit-groupoid clone carrier and its genuine weak original maps

Add one actual original object label and pull back the SAME full Hom
objects, identities and compositions along the canonical fold to the
selected original object. The original full inclusion and projection
have identity Hom maps. Their exact whole triangle and the original DK
weak class prove both SAME maps weak without Kan or cofibrancy premises.
This is the explicit carrier for the unit-groupoid row of Bergner's
actual A2 pushout comparison.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

/-- Fold only the new original label onto the selected SAME original object. -/
def fold (C : Carrier.{u}) (x : C) : C ⊕ PUnit.{u+1} → C := Sum.elim id (fun _ => x)

/-- The actual clone retains the SAME complete original Hom, identity and composition at every folded pair. -/
def fixedObject (C : Carrier.{u}) (x : C) : FixedObjects (C ⊕ PUnit.{u+1}) :=
  CarrierReindexing.object C (fold C x)

/-- Its whole changing-object carrier retains the SAME original full enrichment. -/
abbrev object (C : Carrier.{u}) (x : C) : Carrier.{u} := (fixedObject C x).val

/-- The SAME original individual source object includes at its actual original label. -/
def inclusion (C : Carrier.{u}) (x : C) : C ⟶ object C x where
  obj := Sum.inl
  map _a _b := 𝟙 _
  map_id _a := Category.comp_id _
  map_comp a b c := by
    change eComp SSet.{u} a b c ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet.{u} a b c
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- The actual new original object label of the SAME full clone. -/
def newObject (C : Carrier.{u}) (x : C) : object C x := Sum.inr PUnit.unit

/-- The SAME full original projection is the existing canonical Hom-identity reindexing projection. -/
def projection (C : Carrier.{u}) (x : C) : object C x ⟶ C :=
  CarrierReindexing.toTarget C (fold C x)

/-- Both original full maps recover the SAME original carrier identity. -/
theorem inclusion_projection (C : Carrier.{u}) (x : C) : inclusion C x ≫ projection C x = 𝟙 C := by
  apply EnrichedFunctor.ext SSet.{u} (fun _ => rfl)
  intro a b
  change (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp only [Category.comp_id]

/-- The SAME original projection retains every unchanged original object literally. -/
theorem projection_old (C : Carrier.{u}) (x a : C) : (projection C x).obj (Sum.inl a) = a := rfl

/-- The actual original new label projects to the SAME supplied original object. -/
theorem projection_new (C : Carrier.{u}) (x : C) : (projection C x).obj (newObject C x) = x := rfl

/-- The SAME original inclusion has the full original identity Hom map at every original pair. -/
theorem inclusion_hom (C : Carrier.{u}) (x a b : C) :
    (inclusion C x).map a b = 𝟙 (a ⟶[SSet.{u}] b) := rfl

/-- The SAME original projection has the full original identity Hom map at every actual folded pair. -/
theorem projection_hom (C : Carrier.{u}) (x : C) (a b : object C x) :
    (projection C x).map a b = 𝟙 (fold C x a ⟶[SSet.{u}] fold C x b) := rfl

/-- The actual original clone projection is genuinely DK weak on the SAME original objects and full Homs. -/
theorem projection_weak (C : Carrier.{u}) (x : C) : EnrichedDwyerKan.weakEquivalences (projection C x) := by
  refine ⟨?_, Functor.essSurj_of_surj (fun a => ⟨Sum.inl a, rfl⟩)⟩
  intro a b
  change SSet.realizationWeakEquivalences (𝟙 (fold C x a ⟶[SSet.{u}] fold C x b))
  exact SSet.realizationWeakEquivalences.id_mem _

/-- The SAME original full inclusion is genuinely DK weak by its exact whole original projection triangle. -/
theorem inclusion_weak (C : Carrier.{u}) (x : C) : EnrichedDwyerKan.weakEquivalences (inclusion C x) := by
  have hc : EnrichedDwyerKan.weakEquivalences (inclusion C x ≫ projection C x) :=
    (congrArg (fun F : C ⟶ C => EnrichedDwyerKan.weakEquivalences F) (inclusion_projection C x)).mpr
      (EnrichedDwyerKan.weakEquivalences.id_mem C)
  exact EnrichedDwyerKan.weakEquivalences.of_postcomp _ _ (projection_weak C x) hc

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
