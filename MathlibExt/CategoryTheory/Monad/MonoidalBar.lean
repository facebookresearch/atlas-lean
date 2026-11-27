/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Discrete.Basic
public import MathlibExt.CategoryTheory.Monad.BalancedTensor

/-!
# Two-sided Bar constructions in a monoidal category

A monoid object `M` defines the monad `M ⊗ -`. A left `M`-module `X` and a right action
`Y ⊗ M ⟶ Y` give the two module inputs of the two-sided Bar construction. Its degree-`n` term
is the iterated tensor `Y ⊗ M ⊗ ⋯ ⊗ M ⊗ X`; faces use the two actions and multiplication of
`M`, and degeneracies insert its unit. Compatible module morphisms induce simplicial maps.

When the two degree-one faces have a coequalizer, the balanced tensor product is their
coequalizer and the Bar has the corresponding augmentation. The coequalizer is specified by
`HasCoequalizer`; its universal maps are expressed through balanced pairings.

## References

* J. P. May, *The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics 271,
  Springer, 1972, Chapter 9, Construction 9.6 and Remark 9.12,
  <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

open MonoidalCategory

/-- Tensor-induced monad on `C` from a monoid object. -/
def tensorMonad (M : C) [MonObj M] : Monad C where
  toFunctor := tensorLeft M
  η :=
    { app := fun X => (λ_ X).inv ≫ (MonObj.one ▷ X)
      naturality := fun X Y f => by
        simp only [Functor.id_map]
        calc f ≫ ((λ_ Y).inv ≫ (MonObj.one ▷ Y))
            = (f ≫ (λ_ Y).inv) ≫ (MonObj.one ▷ Y) := by
              rw [Category.assoc]
          _ = ((λ_ X).inv ≫ (𝟙_ C ◁ f)) ≫ (MonObj.one ▷ Y) := by
              rw [leftUnitor_inv_naturality]
          _ = (λ_ X).inv ≫ ((𝟙_ C ◁ f) ≫ (MonObj.one ▷ Y)) := by
              rw [Category.assoc]
          _ = (λ_ X).inv ≫ ((MonObj.one ▷ X) ≫ (M ◁ f)) := by
              rw [whisker_exchange]
          _ = ((λ_ X).inv ≫ (MonObj.one ▷ X)) ≫ (M ◁ f) := by
              rw [← Category.assoc] }
  μ :=
    { app := fun X =>
        (tensorLeftTensor M M).inv.app X ≫ (MonObj.mul ▷ X)
      naturality := fun X Y f => by
        simp only [Functor.comp_map]
        have hInv : (M ◁ (M ◁ f)) ≫ (tensorLeftTensor M M).inv.app Y =
            (tensorLeftTensor M M).inv.app X ≫ ((M ⊗ M) ◁ f) := by
          simp only [tensorLeftTensor_inv_app]
          exact associator_inv_naturality_right M M f
        calc (M ◁ (M ◁ f)) ≫
              ((tensorLeftTensor M M).inv.app Y ≫ (MonObj.mul ▷ Y))
            = ((M ◁ (M ◁ f)) ≫ (tensorLeftTensor M M).inv.app Y) ≫
              (MonObj.mul ▷ Y) := by rw [Category.assoc]
          _ = ((tensorLeftTensor M M).inv.app X ≫ ((M ⊗ M) ◁ f)) ≫
              (MonObj.mul ▷ Y) := by rw [hInv]
          _ = (tensorLeftTensor M M).inv.app X ≫
              (((M ⊗ M) ◁ f) ≫ (MonObj.mul ▷ Y)) := by
              rw [← Category.assoc]
          _ = (tensorLeftTensor M M).inv.app X ≫
              ((MonObj.mul ▷ X) ≫ (M ◁ f)) := by
              rw [whisker_exchange]
          _ = ((tensorLeftTensor M M).inv.app X ≫ (MonObj.mul ▷ X)) ≫
              (M ◁ f) := by rw [Category.assoc] }
  assoc := fun X => by
    dsimp only [tensorLeft, curriedTensor]
    simp only [tensorLeftTensor_inv_app, whiskerLeft_comp, ← Category.assoc]
    have hW : (M ◁ (MonObj.mul ▷ X)) =
        (α_ M (M ⊗ M) X).inv ≫ ((M ◁ MonObj.mul) ▷ X) ≫
          (α_ M M X).hom := by
      have h := whisker_assoc M (MonObj.mul : M ⊗ M ⟶ M) X
      rw [h]
      simp [Category.assoc]
    rw [hW]
    simp only [← Category.assoc]
    have hR : (MonObj.mul ▷ (M ⊗ X)) =
        (α_ (M ⊗ M) M X).inv ≫ ((MonObj.mul ▷ M) ▷ X) ≫
          (α_ M M X).hom := by
      have h := whiskerRight_tensor (MonObj.mul : M ⊗ M ⟶ M) M X
      exact h
    rw [hR]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hMul := MonObj.mul_assoc M
    have hWhisk := congrArg (· ▷ X) hMul
    simp only [comp_whiskerRight] at hWhisk
    rw [hWhisk]
    have hPent : (M ◁ (α_ M M X).inv) ≫ (α_ M (M ⊗ M) X).inv ≫
        (α_ M M M).inv ▷ X =
        (α_ M M (M ⊗ X)).inv ≫ (α_ (M ⊗ M) M X).inv := pentagon_inv
    have hLead : (M ◁ (α_ M M X).inv) ≫ (α_ M (M ⊗ M) X).inv =
        ((α_ M M (M ⊗ X)).inv ≫ (α_ (M ⊗ M) M X).inv) ≫
          ((α_ M M M).hom ▷ X) := by
      rw [← hPent, Category.assoc, Category.assoc, ← comp_whiskerRight,
        Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    simp only [← Category.assoc]
    rw [hLead]
  left_unit := fun X => by
    dsimp only [tensorLeft, curriedTensor]
    simp only [tensorLeftTensor_inv_app, ← Category.assoc]
    have hR : (MonObj.one ▷ (M ⊗ X)) =
        (α_ (𝟙_ C) M X).inv ≫ ((MonObj.one ▷ M) ▷ X) ≫
          (α_ M M X).hom := by
      have h := whiskerRight_tensor (MonObj.one : 𝟙_ C ⟶ M) M X
      exact h
    rw [hR]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hOne := MonObj.one_mul M
    have h := congrArg (· ▷ X) hOne
    simp only [comp_whiskerRight] at h
    rw [h]
    simp
  right_unit := fun X => by
    dsimp only [tensorLeft, curriedTensor]
    simp only [tensorLeftTensor_inv_app, whiskerLeft_comp, ← Category.assoc]
    have hW : (M ◁ (MonObj.one ▷ X)) =
        (α_ M (𝟙_ C) X).inv ≫ ((M ◁ MonObj.one) ▷ X) ≫
          (α_ M M X).hom := by
      have h := whisker_assoc M (MonObj.one : 𝟙_ C ⟶ M) X
      rw [h]
      simp [Category.assoc]
    rw [hW]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hOne := MonObj.mul_one M
    have h := congrArg (· ▷ X) hOne
    simp only [comp_whiskerRight] at h
    rw [h]
    simp

/-- Unit of the tensor monad is the unitor inverse then `one`. -/
@[simp]
theorem tensorMonad_eta_app (M : C) [MonObj M] (X : C) :
    (tensorMonad M).η.app X = (λ_ X).inv ≫ (MonObj.one ▷ X) :=
  rfl

/-- Multiplication uses `tensorLeftTensor` then `mul`. -/
@[simp]
theorem tensorMonad_mu_app (M : C) [MonObj M] (X : C) :
    (tensorMonad M).μ.app X =
      (tensorLeftTensor M M).inv.app X ≫ (MonObj.mul ▷ X) :=
  rfl

/-- Point-valued left module at `X` from a left action. -/
def leftPointModule (M X : C) [MonObj M] [ModObj M X] :
    LeftModule (Discrete PUnit.{1}) (tensorMonad M) :=
  LeftModule.mk ((Functor.const (Discrete PUnit.{1})).obj X)
    { app := fun _ => ModObj.smul (M := M) (X := X)
      naturality := fun _ _ _ => by
        simp only [Functor.comp_map, Functor.const_obj_map]
        dsimp only [tensorMonad, tensorLeft, curriedTensor, Functor.comp,
          Functor.const]
        rw [MonoidalCategory.whiskerLeft_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm }
    (fun _ => by
      simp only [Functor.const_obj_obj]
      have h := ModObj.one_smul_self M X
      change ((λ_ X).inv ≫ (MonObj.one ▷ X)) ≫ ModObj.smul (M := M) (X := X) =
        𝟙 X
      rw [Category.assoc, h, Iso.inv_hom_id])
    (fun _ => by
      simp only [Functor.const_obj_obj]
      have h := ModObj.mul_smul_self M X
      change ((tensorLeftTensor M M).inv.app X ≫ (MonObj.mul ▷ X)) ≫
        ModObj.smul (M := M) (X := X) =
        (M ◁ ModObj.smul (M := M) (X := X)) ≫ ModObj.smul (M := M) (X := X)
      rw [Category.assoc, h, tensorLeftTensor_inv_app]
      rw [Iso.inv_hom_id_assoc])

/-- Functor of the point left module is constant at `X`. -/
@[simp]
theorem leftPointModule_functor (M X : C) [MonObj M] [ModObj M X] :
    (leftPointModule M X).functor =
      (Functor.const (Discrete PUnit.{1})).obj X :=
  rfl

/-- Action of the point module is the left `smul`. -/
@[simp]
theorem leftPointModule_action_app (M X : C) [MonObj M] [ModObj M X]
    (a : Discrete PUnit.{1}) :
    (leftPointModule M X).action.app a = ModObj.smul (M := M) (X := X) :=
  rfl

/-- Right module on `Y ⊗ -` from an explicit right action datum. -/
def rightModuleOfRightAction (Y M : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one : (Y ◁ MonObj.one) ≫ ract = (ρ_ Y).hom)
    (h_assoc : (α_ Y M M).hom ≫ (Y ◁ MonObj.mul) ≫ ract =
      (ract ▷ M) ≫ ract) : RightModule (tensorMonad M) C :=
  RightModule.mk (tensorLeft Y)
    { app := fun Z => (α_ Y M Z).inv ≫ (ract ▷ Z)
      naturality := fun X Z f => by
        change ((Y ◁ (M ◁ f)) ≫ ((α_ Y M Z).inv ≫ (ract ▷ Z))) =
          (((α_ Y M X).inv ≫ (ract ▷ X)) ≫ (Y ◁ f))
        calc ((Y ◁ (M ◁ f)) ≫ ((α_ Y M Z).inv ≫ (ract ▷ Z)))
            = ((((Y ◁ (M ◁ f)) ≫ (α_ Y M Z).inv)) ≫ (ract ▷ Z)) := by
              rw [← Category.assoc]
          _ = ((((α_ Y M X).inv ≫ ((Y ⊗ M) ◁ f))) ≫ (ract ▷ Z)) := by
              rw [associator_inv_naturality_right]
          _ = (((α_ Y M X).inv ≫ (((Y ⊗ M) ◁ f) ≫ (ract ▷ Z)))) := by
              rw [Category.assoc]
          _ = (((α_ Y M X).inv ≫ (((ract ▷ X) ≫ (Y ◁ f))))) := by
              rw [whisker_exchange]
          _ = ((((α_ Y M X).inv ≫ (ract ▷ X))) ≫ ((Y ◁ f))) := by
              rw [← Category.assoc] }
    (fun Z => by
      have hW5 : (Y ◁ (MonObj.one ▷ Z))
          = (α_ Y (𝟙_ C) Z).inv ≫ ((Y ◁ MonObj.one) ▷ Z) ≫
            (α_ Y M Z).hom := by
        rw [whisker_assoc Y (MonObj.one : (𝟙_ C) ⟶ M) Z]
        simp [Category.assoc]
      have eW : (Y ◁ (MonObj.one ▷ Z)) ≫ (α_ Y M Z).inv
          = (α_ Y (𝟙_ C) Z).inv ≫ ((Y ◁ MonObj.one) ▷ Z) := by
        rw [hW5]
        simp only [Category.assoc]
        rw [Iso.hom_inv_id, Category.comp_id]
      have eTri : (Y ◁ (λ_ Z).inv) ≫ (α_ Y (𝟙_ C) Z).inv
          = (ρ_ Y).inv ▷ Z := by
        rw [← triangle_assoc_comp_right_inv, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      change (Y ◁ ((λ_ Z).inv ≫ (MonObj.one ▷ Z))) ≫
        ((α_ Y M Z).inv ≫ (ract ▷ Z)) = 𝟙 (Y ⊗ Z)
      calc (Y ◁ ((λ_ Z).inv ≫ (MonObj.one ▷ Z))) ≫
              ((α_ Y M Z).inv ≫ (ract ▷ Z))
          = (Y ◁ (λ_ Z).inv) ≫
              (((Y ◁ (MonObj.one ▷ Z)) ≫
                ((α_ Y M Z).inv ≫ (ract ▷ Z)))) := by
              rw [whiskerLeft_comp, Category.assoc]
          _ = (Y ◁ (λ_ Z).inv) ≫
              ((((Y ◁ (MonObj.one ▷ Z)) ≫ (α_ Y M Z).inv)) ≫
                (ract ▷ Z)) := by
              exact congrArg _ (Category.assoc _ _ _).symm
          _ = (Y ◁ (λ_ Z).inv) ≫
              ((((α_ Y (𝟙_ C) Z).inv ≫ ((Y ◁ MonObj.one) ▷ Z))) ≫
                (ract ▷ Z)) := by
              rw [eW]
          _ = ((((Y ◁ (λ_ Z).inv) ≫ (α_ Y (𝟙_ C) Z).inv) ≫
              ((Y ◁ MonObj.one) ▷ Z)) ≫ (ract ▷ Z)) := by
              simp only [← Category.assoc]
          _ = ((((ρ_ Y).inv ▷ Z) ≫ ((Y ◁ MonObj.one) ▷ Z)) ≫
              (ract ▷ Z)) := by
              rw [eTri]
          _ = (((ρ_ Y).inv ▷ Z) ≫
              ((((Y ◁ MonObj.one) ▷ Z) ≫ (ract ▷ Z)))) := by
              rw [Category.assoc]
          _ = (((ρ_ Y).inv ▷ Z)) ≫ (((ρ_ Y).hom ▷ Z)) := by
              rw [← comp_whiskerRight, h_one]
          _ = 𝟙 (Y ⊗ Z) := by
              rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight])
    (fun Z => by
      have hWM : (Y ◁ (MonObj.mul ▷ Z))
          = (α_ Y (M ⊗ M) Z).inv ≫ ((Y ◁ MonObj.mul) ▷ Z) ≫
            (α_ Y M Z).hom := by
        rw [whisker_assoc Y (MonObj.mul : M ⊗ M ⟶ M) Z]
        simp [Category.assoc]
      have eWM : (Y ◁ (MonObj.mul ▷ Z)) ≫ (α_ Y M Z).inv
          = (α_ Y (M ⊗ M) Z).inv ≫ ((Y ◁ MonObj.mul) ▷ Z) := by
        rw [hWM]
        simp only [Category.assoc]
        rw [Iso.hom_inv_id, Category.comp_id]
      have hPentY : (Y ◁ (α_ M M Z).inv) ≫ (α_ Y (M ⊗ M) Z).inv ≫
          (α_ Y M M).inv ▷ Z =
          (α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv := pentagon_inv
      have hLeadY : (Y ◁ (α_ M M Z).inv) ≫ (α_ Y (M ⊗ M) Z).inv =
          ((α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv) ≫
            ((α_ Y M M).hom ▷ Z) := by
        rw [← hPentY, Category.assoc, Category.assoc, ← comp_whiskerRight,
          Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
      have eNat : (α_ (Y ⊗ M) M Z).inv ≫ ((ract ▷ M) ▷ Z)
          = (ract ▷ (M ⊗ Z)) ≫ (α_ Y M Z).inv :=
        (associator_inv_naturality_left ract M Z).symm
      change (Y ◁ ((tensorLeftTensor M M).inv.app Z ≫ (MonObj.mul ▷ Z))) ≫
          ((α_ Y M Z).inv ≫ (ract ▷ Z)) =
          (((α_ Y M (M ⊗ Z)).inv ≫ (ract ▷ (M ⊗ Z))) ≫
            ((α_ Y M Z).inv ≫ (ract ▷ Z)))
      calc (Y ◁ ((tensorLeftTensor M M).inv.app Z ≫ (MonObj.mul ▷ Z))) ≫
              ((α_ Y M Z).inv ≫ (ract ▷ Z))
          = (Y ◁ (tensorLeftTensor M M).inv.app Z) ≫
              (((Y ◁ (MonObj.mul ▷ Z)) ≫
                ((α_ Y M Z).inv ≫ (ract ▷ Z)))) := by
              rw [whiskerLeft_comp, Category.assoc]
          _ = (Y ◁ (tensorLeftTensor M M).inv.app Z) ≫
              ((((Y ◁ (MonObj.mul ▷ Z)) ≫ (α_ Y M Z).inv)) ≫
                (ract ▷ Z)) := by
              nth_rw 2 [← Category.assoc]
          _ = (Y ◁ (tensorLeftTensor M M).inv.app Z) ≫
              ((((α_ Y (M ⊗ M) Z).inv ≫ ((Y ◁ MonObj.mul) ▷ Z))) ≫
                (ract ▷ Z)) := by
              rw [eWM]
          _ = (Y ◁ (α_ M M Z).inv) ≫
              ((((α_ Y (M ⊗ M) Z).inv ≫ ((Y ◁ MonObj.mul) ▷ Z))) ≫
                (ract ▷ Z)) := by
              rw [tensorLeftTensor_inv_app]
          _ = (((Y ◁ (α_ M M Z).inv) ≫ (α_ Y (M ⊗ M) Z).inv)) ≫
              ((((Y ◁ MonObj.mul) ▷ Z) ≫ (ract ▷ Z))) := by
              rw [Category.assoc, ← Category.assoc]
          _ = ((((α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv) ≫
              ((α_ Y M M).hom ▷ Z))) ≫
              ((((Y ◁ MonObj.mul) ▷ Z) ≫ (ract ▷ Z))) := by
              rw [hLeadY]
          _ = ((α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv) ≫
              ((((α_ Y M M).hom ≫ ((Y ◁ MonObj.mul) ≫ ract)) ▷ Z)) := by
              rw [Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight]
          _ = ((α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv) ≫
              (((((ract ▷ M) ≫ ract)) ▷ Z)) := by
              rw [h_assoc]
          _ = ((α_ Y M (M ⊗ Z)).inv ≫ (α_ (Y ⊗ M) M Z).inv) ≫
              ((((ract ▷ M) ▷ Z) ≫ (ract ▷ Z))) := by
              rw [comp_whiskerRight]
          _ = ((α_ Y M (M ⊗ Z)).inv ≫
              (((α_ (Y ⊗ M) M Z).inv ≫ ((ract ▷ M) ▷ Z)) ≫
                (ract ▷ Z))) := by
              simp only [Category.assoc]
          _ = ((α_ Y M (M ⊗ Z)).inv ≫
              ((((ract ▷ (M ⊗ Z)) ≫ (α_ Y M Z).inv)) ≫
                (ract ▷ Z))) := by
              rw [eNat]
          _ = (((α_ Y M (M ⊗ Z)).inv ≫ (ract ▷ (M ⊗ Z)))) ≫
              (((α_ Y M Z).inv ≫ (ract ▷ Z))) := by
              simp only [Category.assoc])

/-- Functor of the outer right module is left tensor with `Y`. -/
@[simp]
theorem rightModuleOfRightAction_functor (Y M : C) [MonObj M]
    (ract : Y ⊗ M ⟶ Y) (h_one h_assoc) :
    (rightModuleOfRightAction Y M ract h_one h_assoc).functor =
      tensorLeft Y :=
  rfl

/-- Outer action is the associator inverse then `ract`. -/
@[simp]
theorem rightModuleOfRightAction_action_app (Y M : C) [MonObj M]
    (ract : Y ⊗ M ⟶ Y) (h_one h_assoc) (Z : C) :
    (rightModuleOfRightAction Y M ract h_one h_assoc).action.app Z =
      (α_ Y M Z).inv ≫ (ract ▷ Z) :=
  rfl

/-- Monoidal two-sided bar as the general `twoSidedBar` specialization. -/
noncomputable abbrev monoidalBar (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one : (Y ◁ MonObj.one) ≫ ract = (ρ_ Y).hom)
    (h_assoc : (α_ Y M M).hom ≫ (Y ◁ MonObj.mul) ≫ ract =
      (ract ▷ M) ≫ ract) [ModObj M X] :
    SimplicialObject (Discrete PUnit.{1} ⥤ C) :=
  twoSidedBar (tensorMonad M)
    (rightModuleOfRightAction Y M ract h_one h_assoc) (leftPointModule M X)

/-- Degree `n` of the monoidal bar is the general `barObj`. -/
@[simp]
theorem monoidalBar_obj_op_mk (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) :
    (monoidalBar Y M X ract h_one h_assoc).obj
        (Opposite.op (SimplexCategory.mk n)) =
      barObj (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X) n :=
  rfl

/-- Pointwise degree formula inherits `barObj_obj`. -/
@[simp]
theorem monoidalBar_obj_point (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) (a : Discrete PUnit.{1}) :
    ((monoidalBar Y M X ract h_one h_assoc).obj
      (Opposite.op (SimplexCategory.mk n))).obj a =
      (tensorLeft Y).obj
        ((monadPow (tensorMonad M) n).obj X) :=
  rfl

/-- Zeroth face is the outer iterated action, by the general API. -/
theorem monoidalBar_d0 (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) (a : Discrete PUnit.{1}) :
    ((monoidalBar Y M X ract h_one h_assoc).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).app a =
      barFaceApp (R := rightModuleOfRightAction Y M ract h_one h_assoc)
        (L := leftPointModule M X) n 0 a := by
  simp only [monoidalBar]
  rw [twoSidedBar_map_δ_op_app]

/-- Last face uses the left `X`-action, by the general API. -/
theorem monoidalBar_dLast (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) (a : Discrete PUnit.{1}) :
    ((monoidalBar Y M X ract h_one h_assoc).map
      (SimplexCategory.δ (Fin.last (n + 1))).op).app a =
      barFaceApp (R := rightModuleOfRightAction Y M ract h_one h_assoc)
        (L := leftPointModule M X) n (Fin.last (n + 1)) a := by
  simp only [monoidalBar]
  rw [twoSidedBar_map_δ_op_app]

/-- Interior faces use monad multiplication, by the general API. -/
theorem monoidalBar_dInterior (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) (k : Fin n)
    (a : Discrete PUnit.{1}) :
    ((monoidalBar Y M X ract h_one h_assoc).map
      (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op).app a =
      (tensorLeft Y).map
        (barMuAtPos (tensorMonad M) n k
          ((leftPointModule M X).functor.obj a)) := by
  simp only [monoidalBar]
  rw [twoSidedBar_map_δ_op_app]
  have hk : (k.succ.castSucc : Fin (n + 2)).val = k.val + 1 := by simp
  have h := barFaceApp_of_middle (T := tensorMonad M)
    (R := rightModuleOfRightAction Y M ract h_one h_assoc)
    (L := leftPointModule M X) (a := a) (k := k) hk
  exact h

/-- Degeneracies insert the monad unit, by the general API. -/
theorem monoidalBar_s (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] (n : ℕ) (i : Fin (n + 1))
    (a : Discrete PUnit.{1}) :
    ((monoidalBar Y M X ract h_one h_assoc).map
      (SimplexCategory.σ i).op).app a =
      (tensorLeft Y).map
        (barEtaAtPos (tensorMonad M) n i X) := by
  simp only [monoidalBar]
  rw [twoSidedBar_map_σ_op_app]
  rfl

/-- Outer morphism from a right-compatible map. -/
def rightModuleHomOfRightComp {Y Y' M : C} [MonObj M]
    {ract : Y ⊗ M ⟶ Y} {ract' : Y' ⊗ M ⟶ Y'} (f : Y ⟶ Y')
    (h : (f ▷ M) ≫ ract' = ract ≫ f)
    {h_one : (Y ◁ MonObj.one) ≫ ract = (ρ_ Y).hom}
    {h_assoc : (α_ Y M M).hom ≫ (Y ◁ MonObj.mul) ≫ ract =
      (ract ▷ M) ≫ ract}
    {h_one' : (Y' ◁ MonObj.one) ≫ ract' = (ρ_ Y').hom}
    {h_assoc' : (α_ Y' M M).hom ≫ (Y' ◁ MonObj.mul) ≫ ract' =
      (ract' ▷ M) ≫ ract'} :
    rightModuleOfRightAction Y M ract h_one h_assoc ⟶
      rightModuleOfRightAction Y' M ract' h_one' h_assoc' where
  f :=
    { app := fun Z => f ▷ Z
      naturality := fun _ _ g => whisker_exchange f g }
  h := by
    ext Z
    simp only [NatTrans.comp_app, rightModuleOfRightAction_action_app]
    change f ▷ (M ⊗ Z) ≫ (α_ Y' M Z).inv ≫ (ract' ▷ Z) =
      ((α_ Y M Z).inv ≫ (ract ▷ Z)) ≫ (f ▷ Z)
    have hNat : (f ▷ (M ⊗ Z)) ≫ (α_ Y' M Z).inv =
        (α_ Y M Z).inv ≫ ((f ▷ M) ▷ Z) :=
      associator_inv_naturality_left f M Z
    have hW : ((f ▷ M) ▷ Z) ≫ (ract' ▷ Z) = ((ract ≫ f) ▷ Z) := by
      rw [← comp_whiskerRight, h]
    calc (f ▷ (M ⊗ Z)) ≫ ((α_ Y' M Z).inv ≫ (ract' ▷ Z))
        = (((f ▷ (M ⊗ Z)) ≫ (α_ Y' M Z).inv) ≫ (ract' ▷ Z)) := by
          rw [← Category.assoc]
      _ = (((α_ Y M Z).inv ≫ ((f ▷ M) ▷ Z)) ≫ (ract' ▷ Z)) := by
          rw [hNat]
      _ = ((α_ Y M Z).inv ≫ ((((f ▷ M) ▷ Z) ≫ (ract' ▷ Z)))) := by
          rw [Category.assoc]
      _ = ((α_ Y M Z).inv ≫ (((ract ≫ f) ▷ Z))) := by
          rw [hW]
      _ = ((α_ Y M Z).inv ≫ (((ract ▷ Z) ≫ (f ▷ Z)))) := by
          rw [comp_whiskerRight]
      _ = (((α_ Y M Z).inv ≫ (ract ▷ Z)) ≫ (f ▷ Z)) := by
          rw [← Category.assoc]

/-- Point left-module morphism from an `IsModHom` map. -/
def leftPointModuleHomOfIsModHom {M X X' : C} [MonObj M]
    [ModObj M X] [ModObj M X'] (f : X ⟶ X') [IsModHom M f] :
    leftPointModule M X ⟶ leftPointModule M X' where
  f :=
    { app := fun _ => f
      naturality := fun _ _ _ => by
        simp only [leftPointModule_functor, Functor.const_obj_map]
        exact (Category.id_comp _).trans (Category.comp_id _).symm }
  h := by
    ext a
    simp only [NatTrans.comp_app, leftPointModule_action_app]
    exact (IsModHom.smul_hom (A := M) (f := f)).symm

/-- Identity outer morphism is the module identity. -/
@[simp]
theorem rightModuleHomOfRightComp_id (Y M : C) [MonObj M]
    {ract : Y ⊗ M ⟶ Y}
    {h_one : (Y ◁ MonObj.one) ≫ ract = (ρ_ Y).hom}
    {h_assoc : (α_ Y M M).hom ≫ (Y ◁ MonObj.mul) ≫ ract =
      (ract ▷ M) ≫ ract}
    (h : (𝟙 Y ▷ M) ≫ ract = ract ≫ 𝟙 Y) :
    rightModuleHomOfRightComp (𝟙 Y) h (h_one := h_one)
      (h_assoc := h_assoc) (h_one' := h_one) (h_assoc' := h_assoc) =
      𝟙 _ := by
  ext Z
  simp only [Algebra.id_f]
  exact id_whiskerRight Y Z

/-- Composition of outer morphisms. -/
theorem rightModuleHomOfRightComp_comp {Y Y' Y'' M : C} [MonObj M]
    {ract ract' ract''} (fY : Y ⟶ Y') (gY : Y' ⟶ Y'')
    (hY : (fY ▷ M) ≫ ract' = ract ≫ fY)
    (hY' : (gY ▷ M) ≫ ract'' = ract' ≫ gY)
    {h_one h_assoc h_one' h_assoc' h_one'' h_assoc''}
    (hfg : (fY ≫ gY) ▷ M ≫ ract'' = ract ≫ (fY ≫ gY)) :
    rightModuleHomOfRightComp fY hY (h_one := h_one) (h_assoc := h_assoc)
      (h_one' := h_one') (h_assoc' := h_assoc') ≫
      rightModuleHomOfRightComp gY hY' (h_one := h_one')
        (h_assoc := h_assoc') (h_one' := h_one'') (h_assoc' := h_assoc'') =
      rightModuleHomOfRightComp (fY ≫ gY) hfg (h_one := h_one)
        (h_assoc := h_assoc) (h_one' := h_one'') (h_assoc' := h_assoc'') := by
  ext Z
  simp only [Algebra.comp_f, NatTrans.comp_app]
  exact (comp_whiskerRight fY gY Z).symm

/-- Identity point morphism is the module identity. -/
@[simp]
theorem leftPointModuleHomOfIsModHom_id (M X : C) [MonObj M] [ModObj M X] :
    leftPointModuleHomOfIsModHom (M := M) (𝟙 X) = 𝟙 _ := by
  ext a
  rfl

/-- Composition of point morphisms. -/
theorem leftPointModuleHomOfIsModHom_comp {M X X' X'' : C} [MonObj M]
    [ModObj M X] [ModObj M X'] [ModObj M X'']
    (fX : X ⟶ X') (gX : X' ⟶ X'') [IsModHom M fX] [IsModHom M gX] :
    leftPointModuleHomOfIsModHom (M := M) fX ≫
      leftPointModuleHomOfIsModHom (M := M) gX =
      leftPointModuleHomOfIsModHom (M := M) (fX ≫ gX) := by
  ext a
  rfl

/-- Functoriality of the monoidal bar through `twoSidedBarHom`. -/
noncomputable def monoidalBarHom {Y Y' M X X' : C} [MonObj M]
    {ract : Y ⊗ M ⟶ Y} {ract' : Y' ⊗ M ⟶ Y'} (fY : Y ⟶ Y')
    (hY : (fY ▷ M) ≫ ract' = ract ≫ fY)
    {h_one h_assoc h_one' h_assoc'} [ModObj M X] [ModObj M X']
    (fX : X ⟶ X') [IsModHom M fX] :
    monoidalBar Y M X ract h_one h_assoc ⟶
      monoidalBar Y' M X' ract' h_one' h_assoc' :=
  twoSidedBarHom
    (rightModuleHomOfRightComp fY hY (h_one := h_one) (h_assoc := h_assoc)
      (h_one' := h_one') (h_assoc' := h_assoc'))
    (leftPointModuleHomOfIsModHom fX)

/-- Identity on the monoidal bar, from `twoSidedBarHom_id`. -/
@[simp]
theorem monoidalBarHom_id (Y M X : C) [MonObj M] (ract : Y ⊗ M ⟶ Y)
    (h_one h_assoc) [ModObj M X] :
    monoidalBarHom (𝟙 Y) (by simp) (X := X) (X' := X) (𝟙 X) =
      𝟙 (monoidalBar Y M X ract h_one h_assoc) := by
  simp only [monoidalBarHom, rightModuleHomOfRightComp_id,
    leftPointModuleHomOfIsModHom_id, twoSidedBarHom_id]

/-- Composition on the monoidal bar, from `twoSidedBarHom_comp`. -/
theorem monoidalBarHom_comp {Y Y' Y'' M X X' X'' : C} [MonObj M]
    {ract ract' ract''} (fY : Y ⟶ Y') (gY : Y' ⟶ Y'')
    (hY : (fY ▷ M) ≫ ract' = ract ≫ fY)
    (hY' : (gY ▷ M) ≫ ract'' = ract' ≫ gY)
    {h_one h_assoc h_one' h_assoc' h_one'' h_assoc''}
    [ModObj M X] [ModObj M X'] [ModObj M X'']
    (fX : X ⟶ X') (gX : X' ⟶ X'') [IsModHom M fX] [IsModHom M gX]
    {hfg : (fY ≫ gY) ▷ M ≫ ract'' = ract ≫ (fY ≫ gY)} :
    monoidalBarHom fY hY (h_one := h_one) (h_assoc := h_assoc)
        (h_one' := h_one') (h_assoc' := h_assoc') fX ≫
      monoidalBarHom gY hY' (h_one := h_one') (h_assoc := h_assoc')
        (h_one' := h_one'') (h_assoc' := h_assoc'') gX =
      monoidalBarHom (fY ≫ gY) hfg (h_one := h_one) (h_assoc := h_assoc)
        (h_one' := h_one'') (h_assoc' := h_assoc'') (fX ≫ gX) := by
  simp only [monoidalBarHom]
  rw [twoSidedBarHom_comp, rightModuleHomOfRightComp_comp _ _ _ _ hfg,
    leftPointModuleHomOfIsModHom_comp]

/-- Balanced tensor over the monoidal bar, via the balanced-tensor API. -/
noncomputable abbrev monoidalBalancedTensor (Y M X : C) [MonObj M]
    (ract : Y ⊗ M ⟶ Y) (h_one h_assoc) [ModObj M X]
    [Limits.HasCoequalizer
      (balanceFst (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))
      (balanceSnd (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))] :
    Discrete PUnit.{1} ⥤ C :=
  balancedTensor (tensorMonad M)
    (rightModuleOfRightAction Y M ract h_one h_assoc)
    (leftPointModule M X)

/-- Canonical pairing over the tensor, via the balanced-tensor API. -/
noncomputable def monoidalBalancedPairing (Y M X : C) [MonObj M]
    (ract : Y ⊗ M ⟶ Y) (h_one h_assoc) [ModObj M X]
    [Limits.HasCoequalizer
      (balanceFst (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))
      (balanceSnd (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))] :
    BalancedPairing (tensorMonad M)
      (rightModuleOfRightAction Y M ract h_one h_assoc)
      (leftPointModule M X) :=
  balancedTensorPairing (tensorMonad M)
    (rightModuleOfRightAction Y M ract h_one h_assoc)
    (leftPointModule M X)

/-- Augmented monoidal bar over the coequalizer tensor. -/
noncomputable def monoidalAugmented (Y M X : C) [MonObj M]
    (ract : Y ⊗ M ⟶ Y) (h_one h_assoc) [ModObj M X]
    [Limits.HasCoequalizer
      (balanceFst (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))
      (balanceSnd (tensorMonad M)
        (rightModuleOfRightAction Y M ract h_one h_assoc)
        (leftPointModule M X))] :
    SimplicialObject.Augmented (Discrete PUnit.{1} ⥤ C) :=
  (monoidalBalancedPairing Y M X ract h_one h_assoc).toSimplicialAugmented

end Monad
end CategoryTheory
