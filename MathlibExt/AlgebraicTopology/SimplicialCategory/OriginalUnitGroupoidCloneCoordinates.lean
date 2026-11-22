/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneUnitMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidFunctorReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialHomCongrFullMaps

/-!
# The literal clone retains its SAME original full Hom coordinates

The actual original unit-groupoid map gives the genuine unit-category
isomorphism from the selected old object to the SAME actual new label.
Every full clone Hom is therefore the SAME original folded Hom under
canonical enriched congruence, with identity coefficient maps. Images
of these actual coordinates retain the whole original unit isomorphism.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

/-- The SAME actual unit-groupoid map supplies the full original old-to-new unit isomorphism. -/
def unitCoordinateIso (C : Carrier.{u}) (x : C) :
    ForgetEnrichment.of (C := object C x) SSet.{u} (Sum.inl x : object C x) ≅
      ForgetEnrichment.of (C := object C x) SSet.{u} (newObject C x) :=
  (unitMap C x).forget.mapIso
    (FixedObjects.CodiscreteTerminal.unitIso OriginalTwoLabelUnitGroupoid.labels.{u}
      OriginalTwoLabelUnitGroupoid.source OriginalTwoLabelUnitGroupoid.target)

/-- Every actual clone object retains its SAME old folded original Hom coordinate. -/
def coordinateIso (C : Carrier.{u}) (x : C) : (a : object C x) →
    ForgetEnrichment.of (C := object C x) SSet.{u} (Sum.inl (fold C x a) : object C x) ≅ ForgetEnrichment.of (C :=
      object C x) SSet.{u} a
  | .inl _a => Iso.refl _
  | .inr .unit => unitCoordinateIso C x

/-- Each SAME original forward coordinate has exactly the original full identity coefficient in every scalar degree. -/
theorem coordinateIso_hom_scalar (C : Carrier.{u}) (x : C) (a : object C x) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor (object C x) q).map (coordinateIso C x a).hom =
      (eId SSet.{u} (fold C x a)).app q PUnit.unit := by
  cases a with
  | inl a => exact (SSet.unitScalarFunctor (object C x) q).map_id _
  | inr a => cases a; rfl

/-- Each SAME original inverse coordinate has exactly the original full identity coefficient in every scalar degree. -/
theorem coordinateIso_inv_scalar (C : Carrier.{u}) (x : C) (a : object C x) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor (object C x) q).map (coordinateIso C x a).inv =
      (eId SSet.{u} (fold C x a)).app q PUnit.unit := by
  cases a with
  | inl a => exact (SSet.unitScalarFunctor (object C x) q).map_id _
  | inr a => cases a; rfl

/-- The SAME entire canonical clone Hom-coordinate isomorphism is the literal original identity map. -/
theorem coordinateHom_identity (C : Carrier.{u}) (x : C) (a b : object C x) :
    (Iso.eHomCongr SSet.{u} (coordinateIso C x a) (coordinateIso C x b)).hom =
      𝟙 (fold C x a ⟶[SSet.{u}] fold C x b) := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  have he := SSet.homCongr_scalar (object C x) q (coordinateIso C x a) (coordinateIso C x b) p
  have hc : (SSet.unitScalarFunctor (object C x) q).map (coordinateIso C x a).inv ≫ p ≫
      (SSet.unitScalarFunctor (object C x) q).map (coordinateIso C x b).hom = p := by
    rw [coordinateIso_inv_scalar, coordinateIso_hom_scalar]
    let A : SSet.ScalarObject C q := ⟨fold C x a⟩
    let B : SSet.ScalarObject C q := ⟨fold C x b⟩
    let f : A ⟶ B := p
    change 𝟙 A ≫ f ≫ 𝟙 B = f
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact he.trans hc

/-- Every SAME full original functor image of the clone coordinate retains the actual whole unit-groupoid isomorphism.
-/
theorem unitCoordinateIso_map {C : Carrier.{u}} (x : C) {E : Type v} [EnrichedCategory SSet.{u} E]
    (H : EnrichedFunctor SSet.{u} (object C x) E) :
    H.forget.mapIso (unitCoordinateIso C x) =
      OriginalTwoLabelUnitGroupoid.originalIso ((unitMap C x).comp SSet.{u} H) := by
  apply Iso.ext
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  rfl

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
