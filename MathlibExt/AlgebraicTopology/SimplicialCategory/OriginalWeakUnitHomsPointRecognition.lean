/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerCofibrantCodiscreteResolution

/-!
# Actual point Dwyer–Kan recognition from full original weak unit Homs

The full original projection retains every actual object and every
original Hom-to-unit map. Actual local weakness makes its component
functor fully faithful. The original codiscrete component isomorphisms
then supply both real inverse classes, and the original identity-Hom
triangle proves the SAME original point selection Dwyer–Kan weak.
No Kan condition, interval replacement or global model is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalWeakUnitHomsPointRecognition
variable (C : Carrier.{u})

/-- The actual full original projection keeps every individual object and the literal full Hom-to-unit maps. -/
def projection : C ⟶ CodiscreteEnrichment.object C :=
  CodiscreteEnrichment.extend C C (↾fun x => x)

variable (h : ∀ x y : C,
  SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)))

include h

/-- The SAME entire original projection is locally weak on its full original Hom maps. -/
theorem projection_localWeak : EnrichedDwyerKan.localWeak (projection C) := h

/-- Both real original inverse component classes are read through the SAME full original Hom projection. -/
def componentIso (x y : C) :
    ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y :=
  (EnrichedDwyerKan.componentFullyFaithful (projection C) (projection_localWeak C h)).preimageIso
    (CodiscreteComponentIsomorphisms.iso C ((projection C).obj x) ((projection C).obj y))

/-- The SAME complete original identity Hom is weak through its actual original terminal triangle. -/
theorem identityHom_weak (x : C) : SSet.realizationWeakEquivalences (eId SSet.{u} x) := by
  have he : eId SSet.{u} x ≫ (projection C).map x x = 𝟙 (𝟙_ SSet.{u}) :=
    (projection C).map_id x
  have hc : SSet.realizationWeakEquivalences (eId SSet.{u} x ≫ (projection C).map x x) :=
    (congrArg (fun f : 𝟙_ SSet.{u} ⟶ 𝟙_ SSet.{u} => SSet.realizationWeakEquivalences f) he).mpr
      (SSet.realizationWeakEquivalences.id_mem _)
  exact SSet.realizationWeakEquivalences.of_postcomp _ _ (h x x) hc

/-- Every SAME original point selection is genuinely Dwyer–Kan weak on its original identity Hom and original
objects. -/
theorem point_weak (x : C) : EnrichedDwyerKan.weakEquivalences (BergnerObjects.select x) := by
  constructor
  · intro a b
    exact identityHom_weak C h x
  · refine ⟨fun y => ?_⟩
    exact ⟨PUnit.unit, ⟨componentIso C h x (ComponentCategory.originalObject C y)⟩⟩

end CategoryTheory.SimplicialEnrichment.OriginalWeakUnitHomsPointRecognition
