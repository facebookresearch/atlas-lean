/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceLocalization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWeakUnitHomsPointRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitHomWeakTransport

/-!
# The SAME original point map into the actual equivalence localization is Dwyer–Kan weak

The actual localization construction already proves weakness of every
complete original fixed-label Hom to the unit. Its original endpoint
isomorphisms retain all scalar maps and transfer that conclusion to
every individual original Hom. The SAME original point selection is
therefore genuinely Dwyer–Kan weak. Countable A2 extraction is separate.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- Every SAME full original localization Hom at its actual individual vertices is weak to the original unit. -/
theorem originalHom_toUnit_weak (x y : object a e he) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)) :=
  (CodiscreteEnrichment.toUnit_weak_iff (originalHomIso (fixedObject a e he) x y).hom
    (SSet.realizationWeakEquivalences.of_isIso _)).mpr
      (hom_toUnit_weak a e he (label (fixedObject a e he) x) (label (fixedObject a e he) y))

/-- The SAME actual original point selection into the full localization pullback is genuinely Dwyer–Kan weak. -/
theorem point_weak (x : walking.{u}) :
    EnrichedDwyerKan.weakEquivalences (BergnerObjects.select (vertex (fixedObject a e he) x)) :=
  OriginalWeakUnitHomsPointRecognition.point_weak (object a e he) (originalHom_toUnit_weak a e he)
    (vertex (fixedObject a e he) x)

/-- The original source point retains exactly its supplied original object under the SAME whole projection. -/
theorem sourcePoint_original_obj :
    (toOriginal a e he).obj
      ((BergnerObjects.select (vertex (fixedObject a e he)
        (BergnerTwoObject.source (𝟙_ SSet.{u})))).obj PUnit.unit) =
      a (BergnerTwoObject.source (𝟙_ SSet.{u})) :=
  toOriginal_obj a e he _

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
