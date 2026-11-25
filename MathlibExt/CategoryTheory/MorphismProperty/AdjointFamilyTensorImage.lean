/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
Opaque generic transport of the entire original adjoint-generator family.
The native application supplies every original coefficient map and the proved
free-boundary property. No native property or model is an extra premise there.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe uC vC uD vD w

open CategoryTheory CategoryTheory.MorphismProperty CategoryTheory.MonoidalCategory

namespace CategoryTheory.MorphismProperty.AdjointFamilyTensorImage

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type w}

/-- The full original generator set maps through an actual functor into the target property. -/
theorem adjointGenerators_inverseImage (L : S → C ⥤ D) (I : MorphismProperty C)
    (P : MorphismProperty D) (F : D ⥤ D)
    (h : ∀ a : S, ∀ {X Y : C} (i : X ⟶ Y), I i → P (F.map ((L a).map i))) :
    adjointFamilyGenerators L I ≤ P.inverseImage F :=
  (MorphismProperty.ofHoms_le_iff
    (fun q : S × I.toSet => (L q.1).map q.2.1.hom) (P.inverseImage F)).mpr
      (fun q => h q.1 q.2.1.hom q.2.2)

variable [MonoidalCategory D]

/-- The same complete family retains the literal right-whiskered original maps. -/
theorem adjointGenerators_tensorRight (L : S → C ⥤ D) (I : MorphismProperty C)
    (P : MorphismProperty D) (N : D)
    (h : ∀ a : S, ∀ {X Y : C} (i : X ⟶ Y), I i → P ((L a).map i ▷ N)) :
    adjointFamilyGenerators L I ≤ P.inverseImage (tensorRight N) :=
  adjointGenerators_inverseImage L I P (tensorRight N) h

/-- Applying the whole-family image theorem gives the same original tensor map. -/
theorem tensorRight_image_apply (I P : MorphismProperty D) (N : D)
    (h : I ≤ P.inverseImage (tensorRight N)) {X Y : D} (i : X ⟶ Y) (hi : I i) :
    P (i ▷ N) := h i hi

/-- The whole original braiding Arrow gives the other tensor order in the same property. -/
theorem leftTensor_of_right [BraidedCategory D] (P : MorphismProperty D) [P.RespectsIso]
    (N : D) {X Y : D} (i : X ⟶ Y) (hi : P (i ▷ N)) : P (N ◁ i) := by
  let e : Arrow.mk (i ▷ N) ≅ Arrow.mk (N ◁ i) :=
    Arrow.isoMk (β_ X N) (β_ Y N) (BraidedCategory.braiding_naturality_left i N).symm
  exact (P.arrow_mk_iso_iff e).mp hi

end CategoryTheory.MorphismProperty.AdjointFamilyTensorImage
