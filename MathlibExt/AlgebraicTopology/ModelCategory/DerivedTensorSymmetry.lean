/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorConstructions

/-!
# The actual original symmetry on the chosen derived tensor

The full natural isomorphism uses the original braid on `QX ⊗ QY`, with
both original tensor projection comparisons. Its involution equation is
proved on the entire homotopy category from the same original source maps.

Source: Hovey, *Model Categories*, Theorem 4.3.2.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor BraidedCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The source symmetry is the original braid between the same chosen Q tensor factors. -/
def rawBraiding (d : GeneratedFunctorialReplacements.Data (C := C)) : raw d ≅ (raw d).flip :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun Y => (π).mapIso (β_ (d.Q.obj X) (d.Q.obj Y))) (by
        intro Y Y' g
        change (π).map (d.Q.obj X ◁ d.Q.map g) ≫ (π).map (β_ (d.Q.obj X) (d.Q.obj Y')).hom =
          (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom ≫ (π).map (d.Q.map g ▷ d.Q.obj X)
        rw [← (π).map_comp, ← (π).map_comp]
        exact (π).congr_map (braiding_naturality_right (d.Q.obj X) (d.Q.map g)))) (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      change (π).map (d.Q.map f ▷ d.Q.obj Y) ≫ (π).map (β_ (d.Q.obj X') (d.Q.obj Y)).hom =
        (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom ≫ (π).map (d.Q.obj Y ◁ d.Q.map f)
      rw [← (π).map_comp, ← (π).map_comp]
      exact (π).congr_map (braiding_naturality_left (d.Q.map f) (d.Q.obj Y)))

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The forward source symmetry retains the exact original braid. -/
theorem rawBraiding_hom_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((rawBraiding d).hom.app X).app Y = (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom := rfl

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The inverse source symmetry retains the exact original inverse braid. -/
theorem rawBraiding_inv_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((rawBraiding d).inv.app X).app Y = (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).inv := rfl

/-- The full original symmetry descends to all objects and all morphisms of the chosen derived
tensor. -/
def derivedBraiding (d : GeneratedFunctorialReplacements.Data (C := C)) : tensor d ≅
    (tensor d).flip :=
  Localization.lift₂NatIso π π (weakEquivalences C) (weakEquivalences C)
    (raw d) (raw d).flip (tensor d) (tensor d).flip (rawBraiding d)

/-- The complete derived braid is the original source braid between both actual projection
comparisons. -/
theorem derivedBraiding_hom_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((derivedBraiding d).hom.app ((π).obj X)).app ((π).obj Y) =
      (comparison d X Y).hom ≫ (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom ≫ (comparison d Y X).inv :=
  Localization.lift₂NatTrans_app_app π π (weakEquivalences C) (weakEquivalences C)
    (raw d) (raw d).flip (tensor d) (tensor d).flip (rawBraiding d).hom X Y

/-- The complete inverse derived braid keeps the original inverse source braid and both original
comparisons. -/
theorem derivedBraiding_inv_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((derivedBraiding d).inv.app ((π).obj X)).app ((π).obj Y) =
      (comparison d Y X).hom ≫ (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).inv ≫ (comparison d X Y).inv :=
  Localization.lift₂NatTrans_app_app π π (weakEquivalences C) (weakEquivalences C)
    (raw d).flip (raw d) (tensor d).flip (tensor d) (rawBraiding d).inv X Y

/-- The actual source symmetry has its full original involution equation. -/
theorem derivedBraiding_involutive (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (derivedBraiding d).hom ≫ (flipFunctor Ho Ho Ho).map (derivedBraiding d).hom = 𝟙 (tensor d) :=
        by
  apply Localization.natTrans₂_ext π π (weakEquivalences C) (weakEquivalences C)
  intro X Y
  change ((derivedBraiding d).hom.app ((π).obj X)).app ((π).obj Y) ≫
    ((derivedBraiding d).hom.app ((π).obj Y)).app ((π).obj X) = 𝟙 _
  rw [derivedBraiding_hom_source, derivedBraiding_hom_source]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hBraid : (π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom ≫
      (π).map (β_ (d.Q.obj Y) (d.Q.obj X)).hom = 𝟙 _ := by
    rw [← (π).map_comp, SymmetricCategory.braiding_swap_eq_inv_braiding,
      Iso.inv_hom_id, (π).map_id]
  rw [← Category.assoc ((π).map (β_ (d.Q.obj X) (d.Q.obj Y)).hom)
    ((π).map (β_ (d.Q.obj Y) (d.Q.obj X)).hom) (comparison d X Y).inv,
    hBraid, Category.id_comp, Iso.hom_inv_id]

/-- Every whole homotopy pair retains the same involutive symmetry,
without a source representation choice. -/
theorem derivedBraiding_involutive_app (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : Ho) :
    ((derivedBraiding d).hom.app X).app Y ≫ ((derivedBraiding d).hom.app Y).app X = 𝟙 _ :=
  congrArg (fun t => (t.app X).app Y) (derivedBraiding_involutive d)

end HomotopicalAlgebra.DerivedTensorConstructions
