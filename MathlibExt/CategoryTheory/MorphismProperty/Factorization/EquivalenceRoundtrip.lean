/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# The actual roundtrip of complete original factorization data

The original unit on the Arrow category and the unit on intermediate objects
compare the transported data to the same original functor and maps.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe uC vC uD vD
open CategoryTheory Functor

namespace CategoryTheory

/-- The actual original units compare any complete middle functor with its roundtrip. -/
def originalMiddleRoundtripIso {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (Z : Arrow C ⥤ C) (e : C ≌ D) :
    e.functor.mapArrow ⋙ e.inverse.mapArrow ⋙ Z ⋙ e.functor ⋙ e.inverse ≅ Z :=
  (isoWhiskerLeft (e.functor.mapArrow ⋙ e.inverse.mapArrow)
    (isoWhiskerLeft Z e.unitIso.symm ≪≫ Z.rightUnitor)) ≪≫
      isoWhiskerRight ((Functor.mapArrowEquivalence e).unitIso.symm) Z ≪≫ Z.leftUnitor

/-- The component retains the original middle unit and full original Arrow-unit map. -/
theorem originalMiddleRoundtripIso_hom_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (Z : Arrow C ⥤ C) (e : C ≌ D) (a : Arrow C) :
    (originalMiddleRoundtripIso Z e).hom.app a =
      e.unitIso.inv.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
        Z.map ((Functor.mapArrowEquivalence e).unitIso.inv.app a) := by
  dsimp [originalMiddleRoundtripIso]
  simp only [Category.comp_id]
  rfl

/-- The inverse retains the full original Arrow-unit map and original middle unit. -/
theorem originalMiddleRoundtripIso_inv_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (Z : Arrow C ⥤ C) (e : C ≌ D) (a : Arrow C) :
    (originalMiddleRoundtripIso Z e).inv.app a =
      Z.map ((Functor.mapArrowEquivalence e).unitIso.hom.app a) ≫
        e.unitIso.hom.app (Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) := by
  dsimp [originalMiddleRoundtripIso]
  simp only [Category.id_comp]
  rfl

end CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty C} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The complete actual roundtrip middle functor is compared using the original units. -/
def ofEquivalenceRoundtripComparisonIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) : ((data.ofEquivalence e.symm).ofEquivalence e).Z ≅ data.Z :=
  originalMiddleRoundtripIso data.Z e

/-- Every roundtrip component contains the same original unit and full original Arrow map. -/
theorem ofEquivalenceRoundtripComparisonIso_hom_app
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceRoundtripComparisonIso e).hom.app a =
      e.unitIso.inv.app (data.Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
        data.Z.map ((Functor.mapArrowEquivalence e).unitIso.inv.app a) :=
  originalMiddleRoundtripIso_hom_app data.Z e a

/-- The inverse retains the original full Arrow map and the unit at the original middle. -/
theorem ofEquivalenceRoundtripComparisonIso_inv_app
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceRoundtripComparisonIso e).inv.app a =
      data.Z.map ((Functor.mapArrowEquivalence e).unitIso.hom.app a) ≫
        e.unitIso.hom.app (data.Z.obj (e.inverse.mapArrow.obj (e.functor.mapArrow.obj a))) :=
  originalMiddleRoundtripIso_inv_app data.Z e a

/-- The hom comparison commutes with every complete original Arrow square. -/
theorem ofEquivalence_roundtrip_naturality (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) {a b : Arrow C} (φ : a ⟶ b) :
    ((data.ofEquivalence e.symm).ofEquivalence e).Z.map φ ≫
      (data.ofEquivalenceRoundtripComparisonIso e).hom.app b =
        (data.ofEquivalenceRoundtripComparisonIso e).hom.app a ≫ data.Z.map φ :=
  (data.ofEquivalenceRoundtripComparisonIso e).hom.naturality φ

/-- The inverse comparison commutes with every complete original Arrow square. -/
theorem ofEquivalence_roundtrip_inverse_naturality
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D)
    {a b : Arrow C} (φ : a ⟶ b) :
    data.Z.map φ ≫ (data.ofEquivalenceRoundtripComparisonIso e).inv.app b =
      (data.ofEquivalenceRoundtripComparisonIso e).inv.app a ≫
        ((data.ofEquivalence e.symm).ofEquivalence e).Z.map φ :=
  (data.ofEquivalenceRoundtripComparisonIso e).inv.naturality φ

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
