/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeTensor

/-!
# Public clients of the canonical right-module relative tensor

Install the original right-module monoidal and symmetric structures directly.
The quotient, balanced maps, free comparisons, and equivalence transport are
used through their established public APIs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open scoped CategoryTheory.MonObj

namespace MathlibExtTest.RightModuleRelativeTensorClients

universe uC vC uD vD
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [SymmetricCategory C] (S : C) [MonObj S] [IsCommMonObj S] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

local instance selectedMonoidal : MonoidalCategory (RightModule S) :=
  RightModuleFree.tensorMonoidal S
local instance selectedSymmetric : SymmetricCategory (RightModule S) :=
  RightModuleFree.tensorSymmetric S

/-- The actual quotient balances both complete module actions. -/
theorem projection_balance (X Y : RightModule S) :
    (X.action ▷ Y.X) ≫ RightModuleFree.relativeTensorπ S X Y =
      (α_ X.X S Y.X).hom ≫ (X.X ◁ leftAction S Y) ≫ RightModuleFree.relativeTensorπ S X Y :=
  RightModuleFree.relativeTensorπ_balance S X Y

/-- Both coefficient arrows commute with the original free-tensor comparison. -/
theorem free_tensor_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (RightModuleFree.freeMap S f ⊗ₘ RightModuleFree.freeMap S g) ≫
      (RightModuleFree.freeTensorIso S P' Q').hom =
        (RightModuleFree.freeTensorIso S P Q).hom ≫ RightModuleFree.freeMap S (f ⊗ₘ g) :=
  RightModuleFree.freeTensorIso_naturality S f g

/-- Descent preserves the complete balanced carrier arrow through the quotient. -/
theorem balanced_carrier (X Y Z : RightModule S)
    (h : RightModuleFree.BalancedRightLinearMap S X Y Z) :
    RightModuleFree.relativeTensorπ S X Y ≫
      (RightModuleFree.relativeTensorDescBalanced S X Y Z h).hom = h.hom :=
  RightModuleFree.relativeTensorDescBalanced_π S X Y Z h

/-- Restriction and descent recover the entire balanced map. -/
theorem balanced_recovery (X Y Z : RightModule S)
    (h : RightModuleFree.BalancedRightLinearMap S X Y Z) :
    RightModuleFree.relativeTensorRestrict S X Y Z
      (RightModuleFree.relativeTensorDescBalanced S X Y Z h) = h :=
  RightModuleFree.relativeTensorRestrict_desc S X Y Z h

/-- Descent and restriction recover every original tensor-module arrow. -/
theorem module_hom_recovery (X Y Z : RightModule S) (h : X ⊗ Y ⟶ Z) :
    RightModuleFree.relativeTensorDescBalanced S X Y Z
      (RightModuleFree.relativeTensorRestrict S X Y Z h) = h :=
  RightModuleFree.relativeTensorDesc_restrict S X Y Z h

/-- Input and output maps retain their carrier composition after balanced descent. -/
theorem balanced_composition {X X' Y Y' Z Z' : RightModule S}
    (h : RightModuleFree.BalancedRightLinearMap S X Y Z)
    (f : X' ⟶ X) (g : Y' ⟶ Y) (k : Z ⟶ Z') :
    RightModuleFree.relativeTensorπ S X' Y' ≫
      (RightModuleFree.relativeTensorDescBalanced S X' Y' Z'
        ((h.precompose S f g).postcompose S k)).hom = ((f.hom ⊗ₘ g.hom) ≫ h.hom) ≫ k.hom := by
  rw [RightModuleFree.relativeTensorDescBalanced_π,
    RightModuleFree.BalancedRightLinearMap.postcompose_hom,
    RightModuleFree.BalancedRightLinearMap.precompose_hom]

/-- Both original input arrows act on the full canonical balanced Hom correspondence. -/
theorem hom_naturality_left {X X' Y Y' Z : RightModule S}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⊗ Y ⟶ Z) :
    RightModuleFree.relativeTensorHomEquiv S X' Y' Z ((f ⊗ₘ g) ≫ h) =
      (RightModuleFree.relativeTensorHomEquiv S X Y Z h).precompose S f g :=
  RightModuleFree.relativeTensorHomEquiv_naturality_left S f g h

/-- Every target arrow acts on the same canonical balanced Hom correspondence. -/
theorem hom_naturality_right {X Y Z Z' : RightModule S} (h : X ⊗ Y ⟶ Z) (f : Z ⟶ Z') :
    RightModuleFree.relativeTensorHomEquiv S X Y Z' (h ≫ f) =
      (RightModuleFree.relativeTensorHomEquiv S X Y Z h).postcompose S f :=
  RightModuleFree.relativeTensorHomEquiv_naturality_right S h f

/-- Restricting the braid recovers the original carrier braid and quotient. -/
theorem braid_balanced_carrier (X Y : RightModule S) :
    (RightModuleFree.relativeTensorHomEquiv S X Y (Y ⊗ X) (β_ X Y).hom).hom =
      (β_ X.X Y.X).hom ≫ RightModuleFree.relativeTensorπ S Y X := by
  change RightModuleFree.relativeTensorπ S X Y ≫ (β_ X Y).hom.hom = _
  exact RightModuleFree.relativeTensorBraiding_hom_π S X Y

/-- The selected canonical symmetry is inferred on the original tensor objects. -/
theorem braid_involution (X Y : RightModule S) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

/-- The free tensorator multiplies both full scalar factors after the original quotient. -/
theorem free_tensor_balanced_carrier (P Q : C) :
    (RightModuleFree.relativeTensorHomEquiv S (RightModuleFree.freeObject S P)
      (RightModuleFree.freeObject S Q) (RightModuleFree.freeObject S (P ⊗ Q))
      (RightModuleFree.freeTensorIso S P Q).hom).hom =
        tensorμ P S Q S ≫ ((P ⊗ Q) ◁ MonObj.mul (X := S)) := by
  change RightModuleFree.relativeTensorπ S (RightModuleFree.freeObject S P)
    (RightModuleFree.freeObject S Q) ≫ (RightModuleFree.freeTensorIso S P Q).hom.hom = _
  exact RightModuleFree.freeTensorIso_hom_π S P Q

local instance selectedFreeMonoidal : (RightModuleFree.functor S).Monoidal :=
  RightModuleFree.freeTensorMonoidal S

/-- The original free-functor instance has the complete quotient tensorator. -/
theorem free_functor_tensorator (P Q : C) :
    Functor.LaxMonoidal.μ (RightModuleFree.functor S) P Q =
      (RightModuleFree.freeTensorIso S P Q).hom := rfl

/-- Its original unit map is the inverse of the canonical free-unit comparison. -/
theorem free_functor_unit :
    Functor.LaxMonoidal.ε (RightModuleFree.functor S) = (RightModuleFree.freeTensorUnitIso S).inv := rfl

section Transport

variable {D : Type uD} [Category.{vD} D] (E : RightModule S ≌ D)

/-- A target tensor functor is constructed using only ordinary equivalence transport. -/
def transportedTensorLeft (X : D) : D ⥤ D := by
  letI := Monoidal.transport E
  exact tensorLeft X

/-- The original equivalence unit and canonical quotient retain both source arrows. -/
theorem transported_projection_naturality {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := Monoidal.transport E
    (RightModuleFree.relativeTensorπ S (E.inverse.obj X) (E.inverse.obj Y) ≫
      (E.unitIso.app (E.inverse.obj X ⊗ E.inverse.obj Y)).hom.hom) ≫
        (E.inverse.map (f ⊗ₘ g)).hom =
      ((E.inverse.map f).hom ⊗ₘ (E.inverse.map g).hom) ≫
        (RightModuleFree.relativeTensorπ S (E.inverse.obj X') (E.inverse.obj Y') ≫
          (E.unitIso.app (E.inverse.obj X' ⊗ E.inverse.obj Y')).hom.hom) := by
  let := Monoidal.transport E
  have hu := congrArg Mod.Hom.hom
    (E.unitIso.hom.naturality (E.inverse.map f ⊗ₘ E.inverse.map g))
  rw [Mod.comp_hom', Mod.comp_hom'] at hu
  have hp := RightModuleFree.relativeTensorMap_π S (E.inverse.map f) (E.inverse.map g)
  let p := RightModuleFree.relativeTensorπ S (E.inverse.obj X) (E.inverse.obj Y)
  let p' := RightModuleFree.relativeTensorπ S (E.inverse.obj X') (E.inverse.obj Y')
  let t := (E.inverse.map f ⊗ₘ E.inverse.map g).hom
  let s := (E.inverse.map f).hom ⊗ₘ (E.inverse.map g).hom
  let u := (E.unitIso.app (E.inverse.obj X ⊗ E.inverse.obj Y)).hom.hom
  let u' := (E.unitIso.app (E.inverse.obj X' ⊗ E.inverse.obj Y')).hom.hom
  let r := (E.inverse.map (f ⊗ₘ g)).hom
  change (p ≫ u) ≫ r = s ≫ (p' ≫ u')
  have hUnit : t ≫ u' = u ≫ r := hu
  have hProjection : p ≫ t = s ≫ p' := hp
  exact (Category.assoc p u r).trans
    ((congrArg (fun h => p ≫ h) hUnit.symm).trans
      ((Category.assoc p t u').symm.trans
        ((congrArg (fun h => h ≫ u') hProjection).trans (Category.assoc s p' u'))))

/-- Balanced restriction of transported Hom retains the original unit and inverse functor. -/
theorem transported_balanced_hom_carrier (X Y Z : D) :
    letI := Monoidal.transport E
    ∀ (h : X ⊗ Y ⟶ Z),
    (((E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z).trans
      (RightModuleFree.relativeTensorHomEquiv S
        (E.inverse.obj X) (E.inverse.obj Y) (E.inverse.obj Z))) h).hom =
      RightModuleFree.relativeTensorπ S (E.inverse.obj X) (E.inverse.obj Y) ≫
        (E.unitIso.app (E.inverse.obj X ⊗ E.inverse.obj Y)).hom.hom ≫ (E.inverse.map h).hom := by
  let := Monoidal.transport E
  intro h
  change RightModuleFree.relativeTensorπ S (E.inverse.obj X) (E.inverse.obj Y) ≫
    (E.unitIso.hom.app (E.inverse.obj X ⊗ E.inverse.obj Y) ≫ E.inverse.map h).hom = _
  rw [Mod.comp_hom']
  rfl

/-- The two original Hom equivalences recover every transported arrow. -/
theorem transported_module_hom_recovery (X Y Z : D) :
    letI := Monoidal.transport E
    ∀ (h : X ⊗ Y ⟶ Z),
    ((E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z).trans
      (RightModuleFree.relativeTensorHomEquiv S
        (E.inverse.obj X) (E.inverse.obj Y) (E.inverse.obj Z))).symm
      (((E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z).trans
        (RightModuleFree.relativeTensorHomEquiv S
          (E.inverse.obj X) (E.inverse.obj Y) (E.inverse.obj Z))) h) = h := by
  let := Monoidal.transport E
  intro h
  exact Equiv.symm_apply_apply _ h

end Transport
end MathlibExtTest.RightModuleRelativeTensorClients
