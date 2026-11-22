/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryFramingComparison

/-!
# Original cone-suspension Hom maps and the actual ordinary loop adjunction

The earned natural framing comparison supplies both actual Hom functions.
They retain the original ordinary adjunction, every source and target map,
the chosen zero comparison, and the original generated Q/I cone. No
ordinary-stability equivalence or Hom-bijection outcome is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinarySuspensionHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The actual point-set cone suspension after the same original Q. -/
abbrev coneSuspension : C ⥤ C :=
  GeneratedFunctorialReplacements.Q g ⋙ GeneratedOrdinaryPuppe.suspension g Z hZ

/-- Both original Hom maps are transported through the earned full framing comparison. -/
def homEquiv (X Y : C) :
    ((toHomotopyCategory C).obj ((coneSuspension g Z hZ).obj X) ⟶
      (toHomotopyCategory C).obj Y) ≃
    ((toHomotopyCategory C).obj X ⟶
      (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((toHomotopyCategory C).obj Y)) where
  toFun f := (DerivedSuspensionLoopAdjunction.adjunction
      (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv _ _
    ((GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X ≫ f)
  invFun f := (GeneratedOrdinaryFramingComparison.comparison g Z hZ).hom.app X ≫
    ((DerivedSuspensionLoopAdjunction.adjunction
      (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv
        ((toHomotopyCategory C).obj X) ((toHomotopyCategory C).obj Y)).symm f
  left_inv f := by
    simp only [Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id_app]
    exact Category.id_comp f
  right_inv f := by
    simp only [← Category.assoc, Iso.inv_hom_id_app]
    exact (congrArg
      ((DerivedSuspensionLoopAdjunction.adjunction
        (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv
          ((toHomotopyCategory C).obj X) ((toHomotopyCategory C).obj Y))
      (Category.id_comp _)).trans (Equiv.apply_symm_apply _ f)

/-- The forward function retains the complete original ordinary Hom word and inverse comparison. -/
theorem homEquiv_apply (X Y : C)
    (f : (toHomotopyCategory C).obj ((coneSuspension g Z hZ).obj X) ⟶
      (toHomotopyCategory C).obj Y) :
    homEquiv g Z hZ X Y f =
      (DerivedSuspensionLoopAdjunction.adjunction
        (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv _ _
          ((GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X ≫ f) := rfl

/-- The inverse function retains the original ordinary inverse Hom word and forward comparison. -/
theorem homEquiv_symm_apply (X Y : C)
    (f : (toHomotopyCategory C).obj X ⟶
      (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((toHomotopyCategory C).obj Y)) :
    (homEquiv g Z hZ X Y).symm f =
      (GeneratedOrdinaryFramingComparison.comparison g Z hZ).hom.app X ≫
        ((DerivedSuspensionLoopAdjunction.adjunction
          (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv
            ((toHomotopyCategory C).obj X) ((toHomotopyCategory C).obj Y)).symm f := rfl

/-- Every original source map is retained by the actual forward Hom function. -/
theorem homEquiv_source {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (toHomotopyCategory C).obj ((coneSuspension g Z hZ).obj X') ⟶
      (toHomotopyCategory C).obj Y) :
    homEquiv g Z hZ X Y ((toHomotopyCategory C).map ((coneSuspension g Z hZ).map a) ≫ f) =
      (toHomotopyCategory C).map a ≫ homEquiv g Z hZ X' Y f := by
  have hComparison : (GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X ≫
        (toHomotopyCategory C).map ((coneSuspension g Z hZ).map a) =
      (DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).map
          ((toHomotopyCategory C).map a) ≫
        (GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X' :=
    ((GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.naturality a).symm
  change (DerivedSuspensionLoopAdjunction.adjunction
      (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv _ _
    ((GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X ≫
      ((toHomotopyCategory C).map ((coneSuspension g Z hZ).map a) ≫ f)) = _
  rw [← Category.assoc, hComparison, Category.assoc]
  exact (DerivedSuspensionLoopAdjunction.adjunction
    (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv_naturality_left _ _

/-- Every original target map is retained by the actual forward Hom function. -/
theorem homEquiv_target (X : C) {Y Y' : C} (a : Y ⟶ Y')
    (f : (toHomotopyCategory C).obj ((coneSuspension g Z hZ).obj X) ⟶
      (toHomotopyCategory C).obj Y) :
    homEquiv g Z hZ X Y' (f ≫ (toHomotopyCategory C).map a) =
      homEquiv g Z hZ X Y f ≫
        (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).map
          ((toHomotopyCategory C).map a) := by
  change (DerivedSuspensionLoopAdjunction.adjunction
      (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv _ _
    ((GeneratedOrdinaryFramingComparison.comparison g Z hZ).inv.app X ≫
      (f ≫ (toHomotopyCategory C).map a)) = _
  rw [← Category.assoc]
  exact (DerivedSuspensionLoopAdjunction.adjunction
    (GeneratedFunctorialReplacements.fromGeneration g)).homEquiv_naturality_right _ _

/-- The inverse Hom function retains every original source map as well. -/
theorem homEquiv_symm_source {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (toHomotopyCategory C).obj X' ⟶
      (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((toHomotopyCategory C).obj Y)) :
    (homEquiv g Z hZ X Y).symm ((toHomotopyCategory C).map a ≫ f) =
      (toHomotopyCategory C).map ((coneSuspension g Z hZ).map a) ≫
        (homEquiv g Z hZ X' Y).symm f := by
  apply (homEquiv g Z hZ X Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_source, Equiv.apply_symm_apply]

/-- The inverse Hom function retains every original target map as well. -/
theorem homEquiv_symm_target (X : C) {Y Y' : C} (a : Y ⟶ Y')
    (f : (toHomotopyCategory C).obj X ⟶
      (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((toHomotopyCategory C).obj Y)) :
    (homEquiv g Z hZ X Y').symm
        (f ≫ (DerivedSuspensionLoopAdjunction.loops
          (GeneratedFunctorialReplacements.fromGeneration g)).map ((toHomotopyCategory C).map a)) =
      (homEquiv g Z hZ X Y).symm f ≫ (toHomotopyCategory C).map a := by
  apply (homEquiv g Z hZ X Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_target, Equiv.apply_symm_apply]

end HomotopicalAlgebra.GeneratedOrdinarySuspensionHom
