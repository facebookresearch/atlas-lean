/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.ScalarChange
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceDerivedUnitCriterion

/-!
The source M5 relative-flatness criterion implies the genuine scalar Quillen
equivalence. This is the conditional core; the free-cell producer belongs in
separate constructions and is required before claiming the full M5 article.

The flatness quantifier ranges over all actual right module arrows, with no
cofibrancy requirement on either coefficient endpoint. The scalar unit is
identified through the frozen whole-Arrow comparison, including both quotient
maps and the original scalar bimodule action.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.WeakScalar

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  {A B : C} [MonObj A] [MonObj B] [HasColimitsOfSize.{0, 0} C]

/-- The literal M5 criterion for the existing noncommutative relative tensor. -/
def RelativeFlat (M : Mod C A) : Prop :=
  ∀ {N N' : RightModuleFree.Carrier A} (f : N ⟶ N'),
    weakEquivalences C f.hom →
      weakEquivalences C ((CategoryTheory.Mod.RightLeftTensor.rightTensorFunctor M).map f)

/-- No scalar or right coefficient cofibrancy enters the actual tensor-unit proof. -/
theorem scalarUnit_underlying_weak
    [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (M : Mod C A) (hM : RelativeFlat M) :
    weakEquivalences C ((Mod.ExtensionOfScalars.adjunction p).unit.app M).hom := by
  have ht := hM (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.rightCoefficientMap p) hp
  rw [CategoryTheory.Mod.RightLeftTensor.scalar_rightTensorFunctor_map] at ht
  exact ((weakEquivalences C).arrow_mk_iso_iff
    (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.unitTensorArrowIso p M)).mp ht

section CreatedModels

variable [ModelCategory (Mod C A)] [ModelCategory (Mod C B)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]

omit [ModelCategory (Mod C B)] in
/-- The exact created source class converts the actual underlying unit into a module weak map. -/
theorem scalarUnit_weak
    (hWA : weakEquivalences (Mod C A) =
      (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (M : Mod C A) (hM : RelativeFlat M) :
    WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) := by
  apply (weakEquivalence_iff _).mpr
  rw [hWA]
  exact scalarUnit_underlying_weak p hp M hM

/-- Full scalar weak invariance, with the original cofibrant left-module flatness criterion. -/
theorem isQuillenEquivalenceOfRelativeFlatness
    (hWA : weakEquivalences (Mod C A) =
      (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) =
      (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) =
      (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) =
      (fibrations C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p)
    (hFlat : ∀ M : Mod C A, IsCofibrant M → RelativeFlat M) :
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence := by
  let : (Mod.ExtensionOfScalars.adjunction p).IsQuillenAdjunction :=
    ModuleTransfer.ScalarChange.isQuillen hWA hWB hFA hFB p
  apply Adjunction.IsQuillenEquivalence.mkOfUnitAndCreatesWeakEquivalences
    (Mod.ExtensionOfScalars.adjunction p)
  · intro M hM
    exact scalarUnit_weak hWA p hp M (hFlat M hM)
  · intro X Y f
    simp only [weakEquivalence_iff]
    rw [ModuleTransfer.ScalarChange.restrictionCreatesWeakEquivalences hWA hWB p]
    rfl


end CreatedModels
end HomotopicalAlgebra.ModuleTransfer.WeakScalar
