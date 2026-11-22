/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensor
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-!
# Universal property of the balanced module tensor

For a monoid object `A` in a monoidal category with the stated small
colimits, the balanced tensor of a right module carrier and a left module
is the coequalizer of their two action maps.
`tensorHomEquiv` identifies maps from this tensor with maps from the
underlying tensor that equalize the action maps, giving descent,
uniqueness, and extensionality laws.
For a free left module, the split coequalizer yields `freeTensorIso` to
`N.X ⊗ X`, with formulas for its projection and inverse.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

/-- The first balancing map of the original right-left module tensor. -/
abbrev balancingFst (N : RightModuleFree.Carrier A) (M : Mod C A) :=
  Monad.balanceFst (Monad.tensorMonad A) (rightMonad N) (leftMonad M)

/-- The second balancing map of the original right-left module tensor. -/
abbrev balancingSnd (N : RightModuleFree.Carrier A) (M : Mod C A) :=
  Monad.balanceSnd (Monad.tensorMonad A) (rightMonad N) (leftMonad M)

/-- The evaluated first balancing map on the original tensor carriers. -/
abbrev pointFst (N : RightModuleFree.Carrier A) (M : Mod C A) :=
  (balancingFst N M).app CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point

/-- The evaluated second balancing map on the original tensor carriers. -/
abbrev pointSnd (N : RightModuleFree.Carrier A) (M : Mod C A) :=
  (balancingSnd N M).app CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point

omit [HasColimitsOfSize.{0, 0} C] in
theorem pointFst_formula (N : RightModuleFree.Carrier A) (M : Mod C A) :
    pointFst N M = (α_ N.X A M.X).inv ≫ (rightAction N ▷ M.X) := rfl

omit [HasColimitsOfSize.{0, 0} C] in
theorem pointSnd_formula (N : RightModuleFree.Carrier A) (M : Mod C A) :
    pointSnd N M = N.X ◁ M.mod.smul := rfl

/-- Evaluation preserves the same chosen coequalizer, without a new quotient definition. -/
def tensorCoequalizerIso (N : RightModuleFree.Carrier A) (M : Mod C A) :
    tensorObject N M ≅ coequalizer (pointFst N M) (pointSnd N M) :=
  (PreservesCoequalizer.iso (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.evalPoint (C := C))
    (balancingFst N M) (balancingSnd N M)).symm

theorem projection_coequalizer (N : RightModuleFree.Carrier A) (M : Mod C A) :
    projection N M ≫ (tensorCoequalizerIso N M).hom =
      coequalizer.π (pointFst N M) (pointSnd N M) := by
  change (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.evalPoint (C := C)).map
    (coequalizer.π (balancingFst N M) (balancingSnd N M)) ≫
      (PreservesCoequalizer.iso (CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.evalPoint (C := C))
        (balancingFst N M) (balancingSnd N M)).inv = _
  exact map_π_preserves_coequalizer_inv _ _ _

theorem projection_from_coequalizer (N : RightModuleFree.Carrier A) (M : Mod C A) :
    projection N M =
      coequalizer.π (pointFst N M) (pointSnd N M) ≫ (tensorCoequalizerIso N M).inv := by
  rw [← projection_coequalizer]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance projection_epi (N : RightModuleFree.Carrier A) (M : Mod C A) : Epi (projection N M) := by
  rw [projection_from_coequalizer]
  infer_instance

theorem projection_balance (N : RightModuleFree.Carrier A) (M : Mod C A) :
    pointFst N M ≫ projection N M = pointSnd N M ≫ projection N M := by
  exact congrArg (fun f => f.app CategoryTheory.Mod.ExtensionOfScalars.UnitTensor.point)
    (Monad.balancedTensor_condition (T := Monad.tensorMonad A)
      (R := rightMonad N) (L := leftMonad M))

/-- Every complete balanced underlying map descends through the original quotient. -/
def tensorDesc (N : RightModuleFree.Carrier A) (M : Mod C A) {X : C}
    (k : N.X ⊗ M.X ⟶ X) (hk : pointFst N M ≫ k = pointSnd N M ≫ k) :
    tensorObject N M ⟶ X :=
  (tensorCoequalizerIso N M).hom ≫ coequalizer.desc k hk

theorem projection_tensorDesc (N : RightModuleFree.Carrier A) (M : Mod C A) {X : C}
    (k : N.X ⊗ M.X ⟶ X) (hk : pointFst N M ≫ k = pointSnd N M ≫ k) :
    projection N M ≫ tensorDesc N M k hk = k := by
  unfold tensorDesc
  rw [← Category.assoc, projection_coequalizer, coequalizer.π_desc]

theorem tensor_hom_ext (N : RightModuleFree.Carrier A) (M : Mod C A) {X : C}
    {f g : tensorObject N M ⟶ X} (h : projection N M ≫ f = projection N M ≫ g) :
    f = g := (cancel_epi (projection N M)).mp h

theorem tensorDesc_unique (N : RightModuleFree.Carrier A) (M : Mod C A) {X : C}
    (k : N.X ⊗ M.X ⟶ X) (hk : pointFst N M ≫ k = pointSnd N M ≫ k)
    (f : tensorObject N M ⟶ X) (hf : projection N M ≫ f = k) :
    tensorDesc N M k hk = f := by
  apply tensor_hom_ext N M
  rw [projection_tensorDesc, hf]

/-- The Hom equivalence induced by the original balanced tensor universal property. -/
def tensorHomEquiv (N : RightModuleFree.Carrier A) (M : Mod C A) (X : C) :
    (tensorObject N M ⟶ X) ≃
      {k : N.X ⊗ M.X ⟶ X // pointFst N M ≫ k = pointSnd N M ≫ k} where
  toFun f := ⟨projection N M ≫ f, by
    rw [← Category.assoc, projection_balance, Category.assoc]⟩
  invFun k := tensorDesc N M k.val k.property
  left_inv f := by
    apply tensor_hom_ext N M
    rw [projection_tensorDesc]
  right_inv k := by
    apply Subtype.ext
    exact projection_tensorDesc N M k.val k.property

section Free

omit [HasColimitsOfSize.{0, 0} C] in
theorem freeLeftAction (X : C) :
    ((Mod.free A).obj X).mod.smul = (Monad.tensorMonad A).μ.app X := rfl

omit [HasColimitsOfSize.{0, 0} C] in
theorem free_pointFst (N : RightModuleFree.Carrier A) (X : C) :
    pointFst N ((Mod.free A).obj X) =
      (rightMonad N).action.app ((Monad.tensorMonad A).obj X) := rfl

omit [HasColimitsOfSize.{0, 0} C] in
theorem free_pointSnd (N : RightModuleFree.Carrier A) (X : C) :
    pointSnd N ((Mod.free A).obj X) =
      (rightMonad N).functor.map ((Monad.tensorMonad A).μ.app X) := rfl

/-- The actual free-module balancing pair has its standard absolute split coequalizer. -/
def freeSplitCoequalizer (N : RightModuleFree.Carrier A) (X : C) :
    IsSplitCoequalizer (pointFst N ((Mod.free A).obj X)) (pointSnd N ((Mod.free A).obj X))
      ((rightMonad N).action.app X) where
  rightSection := (rightMonad N).functor.map ((Monad.tensorMonad A).η.app X)
  leftSection := (rightMonad N).functor.map
    ((Monad.tensorMonad A).map ((Monad.tensorMonad A).η.app X))
  condition := (Monad.RightModule.assoc_app (rightMonad N) X).symm
  rightSection_π := Monad.RightModule.unit_app (rightMonad N) X
  leftSection_bottom := by
    rw [free_pointSnd, ← CategoryTheory.Functor.map_comp, (Monad.tensorMonad A).right_unit X]
    exact CategoryTheory.Functor.map_id _ _
  leftSection_top := (rightMonad N).action.naturality ((Monad.tensorMonad A).η.app X)

/-- Reduction to the original right coefficient tensor, proved through its actual split pair. -/
def freeTensorIso (N : RightModuleFree.Carrier A) (X : C) :
    tensorObject N ((Mod.free A).obj X) ≅ N.X ⊗ X where
  hom := tensorDesc N ((Mod.free A).obj X) ((rightMonad N).action.app X)
    (freeSplitCoequalizer N X).condition
  inv := (freeSplitCoequalizer N X).rightSection ≫ projection N ((Mod.free A).obj X)
  hom_inv_id := by
    apply tensor_hom_ext N ((Mod.free A).obj X)
    rw [Category.comp_id]
    change projection N ((Mod.free A).obj X) ≫
      tensorDesc N ((Mod.free A).obj X) ((rightMonad N).action.app X)
        (freeSplitCoequalizer N X).condition ≫
          (freeSplitCoequalizer N X).rightSection ≫ projection N ((Mod.free A).obj X) = _
    rw [← Category.assoc (projection N ((Mod.free A).obj X))
      (tensorDesc N ((Mod.free A).obj X) _ _), projection_tensorDesc]
    rw [← Category.assoc, ← (freeSplitCoequalizer N X).leftSection_top, Category.assoc,
      projection_balance, ← Category.assoc, (freeSplitCoequalizer N X).leftSection_bottom]
    change 𝟙 (N.X ⊗ ((Mod.free A).obj X).X) ≫ projection N ((Mod.free A).obj X) = _
    exact Category.id_comp _
  inv_hom_id := by
    change ((freeSplitCoequalizer N X).rightSection ≫
      projection N ((Mod.free A).obj X)) ≫
        tensorDesc N ((Mod.free A).obj X) ((rightMonad N).action.app X)
          (freeSplitCoequalizer N X).condition = _
    rw [Category.assoc, projection_tensorDesc]
    exact (freeSplitCoequalizer N X).rightSection_π

theorem freeTensorIso_projection (N : RightModuleFree.Carrier A) (X : C) :
    projection N ((Mod.free A).obj X) ≫ (freeTensorIso N X).hom =
      (α_ N.X A X).inv ≫ (rightAction N ▷ X) :=
  projection_tensorDesc N ((Mod.free A).obj X) _ _

theorem freeTensorIso_inv (N : RightModuleFree.Carrier A) (X : C) :
    (freeTensorIso N X).inv =
      (N.X ◁ ((λ_ X).inv ≫ (η[A] ▷ X))) ≫ projection N ((Mod.free A).obj X) := rfl

end Free
end CategoryTheory.Mod.RightLeftTensor
