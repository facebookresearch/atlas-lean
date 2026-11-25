/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation

/-!
# Whole Hom functions of the existing left/right module equivalence

The equivalence is the original `CommutativeModuleConversion.moduleEquivalence`.
Both inverse Hom functions include its original endpoint unit or counit maps.
Their carrier formulas and naturalities use the original recovery isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommutativeModuleConversion

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M]

/-- The entire original unit is the inverse left-module recovery. -/
theorem moduleEquivalence_unit_value :
    (moduleEquivalence M).unitIso = (leftRecoveryNatIso M).symm := rfl

/-- The entire original counit is the right-module recovery. -/
theorem moduleEquivalence_counit_value :
    (moduleEquivalence M).counitIso = rightRecoveryNatIso M := rfl

/-- The actual unit forward map retains the entire carrier identity. -/
theorem moduleEquivalence_unit_hom (X : Mod C M) :
    ((moduleEquivalence M).unitIso.hom.app X).hom = 𝟙 X.X :=
  leftRecoveryIso_inv M X

/-- The actual inverse unit retains the entire carrier identity. -/
theorem moduleEquivalence_unit_inv (X : Mod C M) :
    ((moduleEquivalence M).unitIso.inv.app X).hom = 𝟙 X.X :=
  leftRecoveryIso_hom M X

/-- The actual counit forward map retains the entire carrier identity. -/
theorem moduleEquivalence_counit_hom (X : RightModule M) :
    ((moduleEquivalence M).counitIso.hom.app X).hom = 𝟙 X.X :=
  rightRecoveryIso_hom M X

/-- The actual inverse counit retains the entire carrier identity. -/
theorem moduleEquivalence_counit_inv (X : RightModule M) :
    ((moduleEquivalence M).counitIso.inv.app X).hom = 𝟙 X.X :=
  rightRecoveryIso_inv M X

/-- The full original forward Hom equivalence. -/
def leftHomEquiv (X Y : Mod C M) :
    (X ⟶ Y) ≃ (toRight M X ⟶ toRight M Y) :=
  (moduleEquivalence M).fullyFaithfulFunctor.homEquiv

/-- Its original inverse function retains both actual unit transports. -/
def restoreLeftHom (X Y : Mod C M) (f : toRight M X ⟶ toRight M Y) : X ⟶ Y :=
  (moduleEquivalence M).unitIso.hom.app X ≫ toLeftMap M f ≫
    (moduleEquivalence M).unitIso.inv.app Y

/-- The entire forward function is the original right-module map conversion. -/
theorem leftHomEquiv_toFun (X Y : Mod C M) :
    (leftHomEquiv M X Y).toFun = (fun f => toRightMap M f) := rfl

/-- The entire inverse function uses the original unit comparisons. -/
theorem leftHomEquiv_invFun (X Y : Mod C M) :
    (leftHomEquiv M X Y).invFun = restoreLeftHom M X Y := rfl

/-- Restoring the original forward image recovers the whole module arrow. -/
theorem restoreLeftHom_forward {X Y : Mod C M} (f : X ⟶ Y) :
    restoreLeftHom M X Y (toRightMap M f) = f := (leftHomEquiv M X Y).left_inv f

/-- Converting the restored arrow recovers the whole original right-module arrow. -/
theorem forward_restoreLeftHom {X Y : Mod C M} (f : toRight M X ⟶ toRight M Y) :
    toRightMap M (restoreLeftHom M X Y f) = f := (leftHomEquiv M X Y).right_inv f

/-- The full original inverse-direction Hom equivalence. -/
def rightHomEquiv (X Y : RightModule M) :
    (X ⟶ Y) ≃ (toLeft M X ⟶ toLeft M Y) :=
  (moduleEquivalence M).fullyFaithfulInverse.homEquiv

/-- Its original inverse function retains both actual counit transports. -/
def restoreRightHom (X Y : RightModule M) (f : toLeft M X ⟶ toLeft M Y) : X ⟶ Y :=
  (moduleEquivalence M).counitIso.inv.app X ≫ toRightMap M f ≫
    (moduleEquivalence M).counitIso.hom.app Y

/-- The entire inverse-direction forward function is original left-module conversion. -/
theorem rightHomEquiv_toFun (X Y : RightModule M) :
    (rightHomEquiv M X Y).toFun = (fun f => toLeftMap M f) := rfl

/-- The entire inverse-direction inverse function uses the original counit comparisons. -/
theorem rightHomEquiv_invFun (X Y : RightModule M) :
    (rightHomEquiv M X Y).invFun = restoreRightHom M X Y := rfl

/-- Both inverse-direction functions recover every original right-module arrow. -/
theorem restoreRightHom_forward {X Y : RightModule M} (f : X ⟶ Y) :
    restoreRightHom M X Y (toLeftMap M f) = f := (rightHomEquiv M X Y).left_inv f

/-- Both inverse-direction functions recover every whole converted left-module arrow. -/
theorem forward_restoreRightHom {X Y : RightModule M} (f : toLeft M X ⟶ toLeft M Y) :
    toLeftMap M (restoreRightHom M X Y f) = f := (rightHomEquiv M X Y).right_inv f

/-- Restoring through the original units preserves the entire carrier arrow. -/
theorem restoreLeftHom_hom (X Y : Mod C M) (f : toRight M X ⟶ toRight M Y) :
    (restoreLeftHom M X Y f).hom = f.hom := by
  calc
    (restoreLeftHom M X Y f).hom =
        ((moduleEquivalence M).unitIso.hom.app X).hom ≫
          (toLeftMap M f).hom ≫
            ((moduleEquivalence M).unitIso.inv.app Y).hom := by
      dsimp only [restoreLeftHom, moduleEquivalence, leftToRight, rightToLeft]
      rw [Mod.comp_hom', Mod.comp_hom']
    _ = f.hom := by
      rw [toLeftMap_hom, moduleEquivalence_unit_hom,
        moduleEquivalence_unit_inv]
      exact (Category.id_comp _).trans (Category.comp_id _)

/-- Restoring through the original counits preserves the entire carrier arrow. -/
theorem restoreRightHom_hom (X Y : RightModule M) (f : toLeft M X ⟶ toLeft M Y) :
    (restoreRightHom M X Y f).hom = f.hom := by
  calc
    (restoreRightHom M X Y f).hom =
        ((moduleEquivalence M).counitIso.inv.app X).hom ≫
          (toRightMap M f).hom ≫
            ((moduleEquivalence M).counitIso.hom.app Y).hom := by
      dsimp only [restoreRightHom, moduleEquivalence, leftToRight, rightToLeft]
      rw [Mod.comp_hom', Mod.comp_hom']
    _ = f.hom := by
      rw [toRightMap_hom, moduleEquivalence_counit_inv,
        moduleEquivalence_counit_hom]
      exact (Category.id_comp _).trans (Category.comp_id _)

/-- The whole inverse left Hom function respects composition. -/
theorem restoreLeftHom_comp (X Y Z : Mod C M)
    (f : toRight M X ⟶ toRight M Y) (g : toRight M Y ⟶ toRight M Z) :
    restoreLeftHom M X Z (f ≫ g) = restoreLeftHom M X Y f ≫ restoreLeftHom M Y Z g := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', restoreLeftHom_hom]

/-- The whole inverse right Hom function respects composition. -/
theorem restoreRightHom_comp (X Y Z : RightModule M)
    (f : toLeft M X ⟶ toLeft M Y) (g : toLeft M Y ⟶ toLeft M Z) :
    restoreRightHom M X Z (f ≫ g) = restoreRightHom M X Y f ≫ restoreRightHom M Y Z g := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', restoreRightHom_hom]

/-- Both actual endpoints are retained by the complete inverse left Hom family. -/
theorem restoreLeftHom_naturality (X X' Y Y' : Mod C M)
    (f : X' ⟶ X) (g : Y ⟶ Y') (h : toRight M X ⟶ toRight M Y) :
    restoreLeftHom M X' Y' (toRightMap M f ≫ h ≫ toRightMap M g) =
      f ≫ restoreLeftHom M X Y h ≫ g := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', restoreLeftHom_hom, toRightMap_hom]

/-- Both actual endpoints are retained by the complete inverse right Hom family. -/
theorem restoreRightHom_naturality (X X' Y Y' : RightModule M)
    (f : X' ⟶ X) (g : Y ⟶ Y') (h : toLeft M X ⟶ toLeft M Y) :
    restoreRightHom M X' Y' (toLeftMap M f ≫ h ≫ toLeftMap M g) =
      f ≫ restoreRightHom M X Y h ≫ g := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', restoreRightHom_hom, toLeftMap_hom]

end CategoryTheory.CommutativeModuleConversion
