/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorComputation
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedCofibrantExt
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!
# Coherence of the original chosen derived tensor

The notation carrier below is a type synonym for the same canonical weak
localization. Its tensor, associator, unitors and projection are the previously
constructed actual Q/R functors and maps. Coherence is proved using the actual
ordinary computation on cofibrant objects and the original Q counit naturality.

Source: Hovey, *Model Categories*, Theorem 4.3.2.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A notation type synonym for the original full canonical weak localization. -/
@[nolint unusedArguments]
def MonoidalHo (_d : GeneratedFunctorialReplacements.Data (C := C)) :=
  MorphismProperty.Localization (weakEquivalences C)

namespace MonoidalHo

instance category (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Category.{max u v} (MonoidalHo d) :=
  inferInstanceAs (Category (MorphismProperty.Localization (weakEquivalences C)))

/-- The projection has the exact original object and morphism functions. -/
def projection (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ MonoidalHo d :=
  MorphismProperty.Q (weakEquivalences C)

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

/-- Every monoidal data field is the previously constructed actual derived field. -/
instance monoidalStruct (d : GeneratedFunctorialReplacements.Data (C := C)) :
    MonoidalCategoryStruct (MonoidalHo d) where
  tensorObj X Y := ((tensor d).obj X).obj Y
  whiskerLeft X _ _ f := ((tensor d).obj X).map f
  whiskerRight f Y := ((tensor d).map f).app Y
  tensorUnit := (projection d).obj (𝟙_ C)
  associator X Y Z := (((derivedAssociator d).app X).app Y).app Z
  leftUnitor X := (derivedLeftUnitor d).app X
  rightUnitor X := (derivedRightUnitor d).app X

variable (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The original pushout-product axiom makes the tensor of actual cofibrant sources cofibrant. -/
local instance tensorCofibrant {X Y : C} [IsCofibrant X] [IsCofibrant Y] : IsCofibrant (X ⊗ Y) :=
  tensor_isCofibrant X Y

/-- The exact ordinary computation isomorphism on the original cofibrant endpoints. -/
def μ (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    (projection d).obj X ⊗ (projection d).obj Y ≅ (projection d).obj (X ⊗ Y) :=
  cofibrantComparison d X Y

@[reassoc]
theorem whiskerLeft_comp (X : MonoidalHo d) {Y Z E : MonoidalHo d} (f : Y ⟶ Z) (g : Z ⟶ E) :
    X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g :=
  ((tensor d).obj X).map_comp f g

@[reassoc]
theorem comp_whiskerRight {X Y Z : MonoidalHo d} (f : X ⟶ Y) (g : Y ⟶ Z) (E : MonoidalHo d) :
    (f ≫ g) ▷ E = f ▷ E ≫ g ▷ E := by
  change ((tensor d).map (f ≫ g)).app E = _
  rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  rfl

theorem whiskerLeft_id (X Y : MonoidalHo d) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) :=
  ((tensor d).obj X).map_id Y

theorem id_whiskerRight (X Y : MonoidalHo d) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  change ((tensor d).map (𝟙 X)).app Y = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  rfl

theorem tensorHom_id {X Y : MonoidalHo d} (f : X ⟶ Y) (Z : MonoidalHo d) :
    f ⊗ₘ 𝟙 Z = f ▷ Z := by
  change ((tensor d).map f).app Z ≫ ((tensor d).obj Y).map (𝟙 Z) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem id_tensorHom (X : MonoidalHo d) {Y Z : MonoidalHo d} (f : Y ⟶ Z) :
    𝟙 X ⊗ₘ f = X ◁ f := by
  change ((tensor d).map (𝟙 X)).app Y ≫ ((tensor d).obj X).map f = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

@[reassoc]
theorem whisker_exchange {X X' Y Y' : MonoidalHo d} (f : X ⟶ X') (g : Y ⟶ Y') :
    X ◁ g ≫ f ▷ Y' = f ▷ Y ≫ X' ◁ g :=
  ((tensor d).map f).naturality g

@[reassoc]
theorem associator_naturality_left {X X' : MonoidalHo d} (f : X ⟶ X') (Y Z : MonoidalHo d) :
    (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) :=
  NatTrans.congr_app (NatTrans.congr_app ((derivedAssociator d).hom.naturality f) Y) Z

@[reassoc]
theorem associator_naturality_middle (X : MonoidalHo d) {Y Y' : MonoidalHo d}
    (f : Y ⟶ Y') (Z : MonoidalHo d) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (f ▷ Z) :=
  NatTrans.congr_app (((derivedAssociator d).hom.app X).naturality f) Z

@[reassoc]
theorem associator_naturality_right (X Y : MonoidalHo d) {Z Z' : MonoidalHo d} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) :=
  (((derivedAssociator d).hom.app X).app Y).naturality f

@[reassoc]
theorem μ_natural_left {X X' : C} (f : X ⟶ X') (Y : C)
    [IsCofibrant X] [IsCofibrant X'] [IsCofibrant Y] :
    (projection d).map f ▷ (projection d).obj Y ≫ (μ d X' Y).hom =
      (μ d X Y).hom ≫ (projection d).map (f ▷ Y) :=
  cofibrantComparison_naturality_left d f Y

@[reassoc]
theorem μ_natural_right (X : C) {Y Y' : C} (f : Y ⟶ Y')
    [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Y'] :
    (projection d).obj X ◁ (projection d).map f ≫ (μ d X Y').hom =
      (μ d X Y).hom ≫ (projection d).map (X ◁ f) :=
  cofibrantComparison_naturality_right d X f

@[reassoc]
theorem μ_inv_natural_left {X X' : C} (f : X ⟶ X') (Y : C)
    [IsCofibrant X] [IsCofibrant X'] [IsCofibrant Y] :
    (projection d).map (f ▷ Y) ≫ (μ d X' Y).inv =
      (μ d X Y).inv ≫ (projection d).map f ▷ (projection d).obj Y := by
  apply (cancel_epi (μ d X Y).hom).mp
  rw [← μ_natural_left_assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem μ_inv_natural_right (X : C) {Y Y' : C} (f : Y ⟶ Y')
    [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Y'] :
    (projection d).map (X ◁ f) ≫ (μ d X Y').inv =
      (μ d X Y).inv ≫ (projection d).obj X ◁ (projection d).map f := by
  apply (cancel_epi (μ d X Y).hom).mp
  rw [← μ_natural_right_assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The associator source computation is the exact original associator and both Q-counit
calculations. -/
theorem associator_hom_app (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    letI := tensor_isCofibrant X Y
    letI := tensor_isCofibrant Y Z
    (α_ ((projection d).obj X) ((projection d).obj Y) ((projection d).obj Z)).hom =
      (μ d X Y).hom ▷ (projection d).obj Z ≫ (μ d (X ⊗ Y) Z).hom ≫
        (projection d).map (α_ X Y Z).hom ≫ (μ d X (Y ⊗ Z)).inv ≫
          (projection d).obj X ◁ (μ d Y Z).inv := by
  let _ : IsCofibrant (X ⊗ Y) := tensor_isCofibrant X Y
  let _ : IsCofibrant (Y ⊗ Z) := tensor_isCofibrant Y Z
  change (((derivedAssociator d).hom.app ((weakEquivalences C).Q.obj X)).app
      ((weakEquivalences C).Q.obj Y)).app ((weakEquivalences C).Q.obj Z) =
    ((tensor d).map (cofibrantComparison d X Y).hom).app ((weakEquivalences C).Q.obj Z) ≫
      (cofibrantComparison d (X ⊗ Y) Z).hom ≫ (weakEquivalences C).Q.map (α_ X Y Z).hom ≫
        (cofibrantComparison d X (Y ⊗ Z)).inv ≫
          ((tensor d).obj ((weakEquivalences C).Q.obj X)).map (cofibrantComparison d Y Z).inv
  have h := derivedAssociator_cofibrant d X Y Z
  dsimp [leftCofibrantComparison, rightCofibrantComparison] at h
  simpa only [Category.assoc] using h

/-- The two complete derived pentagon paths agree, from the original point-set pentagon
and the exact ordinary computations on all original cofibrant objects. -/
theorem pentagon_natTrans :
    ofBifunctor.Pentagon.firstMap (tensor d) (derivedAssociator d) =
      ofBifunctor.Pentagon.secondMap (tensor d) (derivedAssociator d) := by
  apply GeneratedFunctorialReplacements.natTrans₄_ext_cofibrant d
  intro X₁ X₂ X₃ X₄ _ _ _ _
  change MonoidalCategory.Pentagon ((projection d).obj X₁) ((projection d).obj X₂)
    ((projection d).obj X₃) ((projection d).obj X₄)
  dsimp [MonoidalCategory.Pentagon]
  have h₂ : (((projection d).obj X₁ ◁ (μ d X₂ X₃).inv) ▷ (projection d).obj X₄) ≫
      (α_ ((projection d).obj X₁) ((projection d).obj X₂ ⊗ (projection d).obj X₃)
        ((projection d).obj X₄)).hom ≫
          (projection d).obj X₁ ◁ ((μ d X₂ X₃).hom ▷ (projection d).obj X₄) =
      (α_ ((projection d).obj X₁) ((projection d).obj (X₂ ⊗ X₃))
        ((projection d).obj X₄)).hom := by
    simp only [associator_naturality_middle_assoc, ← whiskerLeft_comp, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, whiskerLeft_id, Category.comp_id]
  have h₁ : ((((μ d X₁ X₂).hom ▷ (projection d).obj X₃) ▷ (projection d).obj X₄) ≫
      (α_ ((projection d).obj (X₁ ⊗ X₂)) ((projection d).obj X₃)
        ((projection d).obj X₄)).hom ≫
          (μ d X₁ X₂).inv ▷ ((projection d).obj X₃ ⊗ (projection d).obj X₄)) =
      (α_ ((projection d).obj X₁ ⊗ (projection d).obj X₂) ((projection d).obj X₃)
        ((projection d).obj X₄)).hom := by
    simp only [associator_naturality_left_assoc, ← comp_whiskerRight, Iso.hom_inv_id,
      id_whiskerRight, Category.comp_id]
  have h₃ : (((projection d).obj X₁ ⊗ (projection d).obj X₂) ◁ (μ d X₃ X₄).hom) ≫
      (α_ ((projection d).obj X₁) ((projection d).obj X₂)
        ((projection d).obj (X₃ ⊗ X₄))).hom ≫
          (projection d).obj X₁ ◁ ((projection d).obj X₂ ◁ (μ d X₃ X₄).inv) =
      (α_ ((projection d).obj X₁) ((projection d).obj X₂)
        ((projection d).obj X₃ ⊗ (projection d).obj X₄)).hom := by
    simp only [associator_naturality_right_assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, Category.comp_id]
  rw [associator_hom_app, associator_hom_app,
    whiskerLeft_comp, comp_whiskerRight, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc, Category.assoc, comp_whiskerRight, Category.assoc,
    reassoc_of% h₂, associator_hom_app, ← h₁, ← h₃,
    associator_hom_app, associator_hom_app]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, Category.comp_id,
    μ_natural_left_assoc, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (projection d).map_comp_assoc, whiskerLeft_comp, ← μ_inv_natural_right_assoc,
    ← (projection d).map_comp_assoc]
  simp only [Category.assoc, MonoidalCategory.pentagon, CategoryTheory.Functor.map_comp,
    comp_whiskerRight_assoc]
  congr 3
  simp only [← Category.assoc]
  congr
  simp only [← cancel_mono (μ d (X₁ ⊗ X₂) (X₃ ⊗ X₄)).inv, Category.assoc,
    Category.id_comp, whisker_exchange_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, ← whiskerLeft_comp, whiskerLeft_id]

/-- The full derived unit triangle holds with the original tensor unit and actual Q-unit map. -/
theorem triangle_natTrans :
    ofBifunctor.Triangle.firstMap (tensor d) ((projection d).obj (𝟙_ C))
      (derivedAssociator d) (derivedLeftUnitor d) =
    ofBifunctor.Triangle.secondMap (tensor d) ((projection d).obj (𝟙_ C))
      (derivedRightUnitor d) := by
  apply GeneratedFunctorialReplacements.natTrans₂_ext_cofibrant d
  intro X Y _ _
  exact derivedTriangle_cofibrant d X Y

/-- The actual chosen derived tensor, associator and both unitors form a complete monoidal category.
-/
instance monoidalCategory : MonoidalCategory (MonoidalHo d) :=
  MonoidalCategory.ofBifunctor (tensor d) ((projection d).obj (𝟙_ C)) (derivedAssociator d)
    (derivedLeftUnitor d) (derivedRightUnitor d) (pentagon_natTrans d) (triangle_natTrans d)

end MonoidalHo

end HomotopicalAlgebra.DerivedTensorConstructions
