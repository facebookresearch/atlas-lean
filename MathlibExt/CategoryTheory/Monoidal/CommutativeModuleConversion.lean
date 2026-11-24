/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Action.Opposites
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommutativeModuleConversion

/-! Both conversions use positive braidings. They are opposite-direction functors here;
the recovery isomorphisms and inverse equivalence require the symmetric section below. -/

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable (S : C) [MonObj S]

omit [BraidedCategory C] in
/-- The existing module category for the actual right tensor action. -/
abbrev RightModule := CategoryTheory.Mod (C := Cᴹᵒᵖ) C (mop S)

/-- The full right action obtained from an existing left module. -/
def rightAction (M : CategoryTheory.Mod C S) : M.X ⊗ S ⟶ M.X :=
  (β_ M.X S).hom ≫ ModObj.smul (M := S) (X := M.X)

omit [MonObj S] in
@[reassoc] private theorem rightSwap (X : C) :
    (α_ X S S).inv ≫ ((β_ X S).hom ▷ S) ≫ (β_ (S ⊗ X) S).hom =
      (β_ X (S ⊗ S)).hom ≫ ((β_ S S).hom ▷ X) ≫ (α_ S S X).hom := by
  simp only [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc]

omit [MonObj S] in
@[reassoc] private theorem leftSwap (X : C) :
    (α_ S S X).hom ≫ (S ◁ (β_ S X).hom) ≫ (β_ S (X ⊗ S)).hom =
      (β_ (S ⊗ S) X).hom ≫ (X ◁ (β_ S S).hom) ≫ (α_ X S S).inv := by
  simp only [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc]

variable [IsCommMonObj S]

omit [IsCommMonObj S] in
theorem rightAction_one (M : CategoryTheory.Mod C S) :
    (M.X ◁ (η : (𝟙_ C) ⟶ S)) ≫ rightAction S M = (ρ_ M.X).hom := by
  dsimp only [rightAction]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [ModObj.one_smul_self]
  rw [braiding_tensorUnit_right]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem rightAction_mul (M : CategoryTheory.Mod C S) :
    (M.X ◁ (μ : S ⊗ S ⟶ S)) ≫ rightAction S M =
      (α_ M.X S S).inv ≫ (rightAction S M ▷ S) ≫ rightAction S M := by
  let X := M.X
  let l : S ⊗ X ⟶ X := ModObj.smul (M := S) (X := M.X)
  have hL : ((μ : S ⊗ S ⟶ S) ▷ X) ≫ l =
      (α_ S S X).hom ≫ (S ◁ l) ≫ l := ModObj.mul_smul_self S M.X
  change (X ◁ (μ : S ⊗ S ⟶ S)) ≫ (β_ X S).hom ≫ l =
    (α_ X S S).inv ≫ (((β_ X S).hom ≫ l) ▷ S) ≫ (β_ X S).hom ≫ l
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [hL]
  symm
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc, rightSwap_assoc S X]
  rw [← hL, ← MonoidalCategory.comp_whiskerRight_assoc,
    IsCommMonObj.mul_comm]

/-- The original left action derives the actual right module structure. -/
@[instance_reducible]
def rightModObj (M : CategoryTheory.Mod C S) : ModObj (mop S) M.X where
  smul := rightAction S M
  one_smul := by
    change (M.X ◁ (η : (𝟙_ C) ⟶ S)) ≫ rightAction S M = (ρ_ M.X).hom
    exact rightAction_one S M
  mul_smul := by
    change (M.X ◁ (μ : S ⊗ S ⟶ S)) ≫ rightAction S M =
      (α_ M.X S S).inv ≫ (rightAction S M ▷ S) ≫ rightAction S M
    exact rightAction_mul S M

/-- The right module structure retains the entire original braided arrow. -/
theorem rightModObj_smul (M : CategoryTheory.Mod C S) :
    (rightModObj S M).smul = rightAction S M := (rfl)

/-- The original whole object with the derived right module action. -/
@[instance_reducible]
def toRight (M : CategoryTheory.Mod C S) : RightModule S where
  X := M.X
  mod := rightModObj S M

/-- The right action retains the complete original underlying object. -/
theorem toRight_obj (M : CategoryTheory.Mod C S) : (toRight S M).X = M.X := (rfl)

/-- The right module uses the actual braided original action. -/
theorem toRight_smul (M : CategoryTheory.Mod C S) :
    ModObj.smul (M := mop S) (X := (toRight S M).X) = rightAction S M :=
  rightModObj_smul S M

omit [IsCommMonObj S] in
/-- The full left action obtained from an existing right module. -/
def leftAction (M : RightModule S) : S ⊗ M.X ⟶ M.X :=
  (β_ S M.X).hom ≫ ModObj.smul (M := mop S) (X := M.X)

omit [IsCommMonObj S] in
theorem leftAction_one (M : RightModule S) :
    ((η : (𝟙_ C) ⟶ S) ▷ M.X) ≫ leftAction S M = (λ_ M.X).hom := by
  let r : M.X ⊗ S ⟶ M.X := ModObj.smul (M := mop S) (X := M.X)
  have hR : (M.X ◁ (η : (𝟙_ C) ⟶ S)) ≫ r = (ρ_ M.X).hom := by
    exact ModObj.one_smul (M := mop S) (X := M.X)
  change ((η : (𝟙_ C) ⟶ S) ▷ M.X) ≫ (β_ S M.X).hom ≫ r = (λ_ M.X).hom
  rw [BraidedCategory.braiding_naturality_left_assoc, hR, braiding_tensorUnit_left]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem leftAction_mul (M : RightModule S) :
    ((μ : S ⊗ S ⟶ S) ▷ M.X) ≫ leftAction S M =
      (α_ S S M.X).hom ≫ (S ◁ leftAction S M) ≫ leftAction S M := by
  let X := M.X
  let r : X ⊗ S ⟶ X := ModObj.smul (M := mop S) (X := M.X)
  have hR : (X ◁ (μ : S ⊗ S ⟶ S)) ≫ r =
      (α_ X S S).inv ≫ (r ▷ S) ≫ r := by
    exact ModObj.mul_smul (M := mop S) (X := M.X)
  change ((μ : S ⊗ S ⟶ S) ▷ X) ≫ (β_ S X).hom ≫ r =
    (α_ S S X).hom ≫ (S ◁ ((β_ S X).hom ≫ r)) ≫ (β_ S X).hom ≫ r
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [hR]
  symm
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc, leftSwap_assoc S X]
  rw [← hR, ← MonoidalCategory.whiskerLeft_comp_assoc, IsCommMonObj.mul_comm]

/-- The actual right action derives a lawful left module structure. -/
@[instance_reducible]
def leftModObj (M : RightModule S) : ModObj S M.X where
  smul := leftAction S M
  one_smul := by exact leftAction_one S M
  mul_smul := by exact leftAction_mul S M

/-- The left module structure retains the entire original braided arrow. -/
theorem leftModObj_smul (M : RightModule S) :
    (leftModObj S M).smul = leftAction S M := (rfl)

/-- The original whole object with the derived left module action. -/
@[instance_reducible]
def toLeft (M : RightModule S) : CategoryTheory.Mod C S where
  X := M.X
  mod := leftModObj S M

/-- The reverse-direction conversion retains the original whole object. -/
theorem toLeft_obj (M : RightModule S) : (toLeft S M).X = M.X := (rfl)

/-- The reverse-direction conversion uses the actual complete right action. -/
theorem toLeft_smul (M : RightModule S) :
    ModObj.smul (M := S) (X := (toLeft S M).X) = leftAction S M :=
  leftModObj_smul S M

/-- Every left module morphism retains its complete underlying arrow. -/
def toRightMap {M N : CategoryTheory.Mod C S} (f : M ⟶ N) :
    toRight S M ⟶ toRight S N :=
  Mod.Hom.mk' f.hom (by
    change rightAction S M ≫ f.hom = (f.hom ▷ S) ≫ rightAction S N
    dsimp only [rightAction]
    simp only [Category.assoc]
    have h : ModObj.smul (M := S) (X := M.X) ≫ f.hom =
        (S ◁ f.hom) ≫ ModObj.smul (M := S) (X := N.X) :=
      IsModHom.smul_hom (A := S) (f := f.hom)
    rw [h, BraidedCategory.braiding_naturality_left_assoc])

/-- The forward conversion keeps every entire original module map. -/
theorem toRightMap_hom {M N : CategoryTheory.Mod C S} (f : M ⟶ N) :
    (toRightMap S f).hom = f.hom := (rfl)

/-- Every right module morphism retains its complete underlying arrow. -/
def toLeftMap {M N : RightModule S} (f : M ⟶ N) :
    toLeft S M ⟶ toLeft S N :=
  Mod.Hom.mk' f.hom (by
    change leftAction S M ≫ f.hom = (S ◁ f.hom) ≫ leftAction S N
    let rM : M.X ⊗ S ⟶ M.X := ModObj.smul (M := mop S) (X := M.X)
    let rN : N.X ⊗ S ⟶ N.X := ModObj.smul (M := mop S) (X := N.X)
    have h : rM ≫ f.hom = (f.hom ▷ S) ≫ rN :=
      IsModHom.smul_hom (A := mop S) (f := f.hom)
    dsimp only [leftAction]
    change ((β_ S M.X).hom ≫ rM) ≫ f.hom = (S ◁ f.hom) ≫ (β_ S N.X).hom ≫ rN
    simp only [Category.assoc]
    rw [h, BraidedCategory.braiding_naturality_right_assoc])

/-- The reverse-direction conversion keeps every entire original module map. -/
theorem toLeftMap_hom {M N : RightModule S} (f : M ⟶ N) :
    (toLeftMap S f).hom = f.hom := (rfl)

/-- The complete forward conversion is an ordinary module functor. -/
def leftToRight : CategoryTheory.Mod C S ⥤ RightModule S where
  obj := toRight S
  map := toRightMap S
  map_id M := by
    apply Mod.hom_ext
    rw [toRightMap_hom]
    rfl
  map_comp f g := by
    apply Mod.hom_ext
    change (toRightMap S (f ≫ g)).hom = (toRightMap S f).hom ≫ (toRightMap S g).hom
    rw [toRightMap_hom, toRightMap_hom, toRightMap_hom]
    rfl

/-- The complete reverse-direction conversion is an ordinary module functor. -/
def rightToLeft : RightModule S ⥤ CategoryTheory.Mod C S where
  obj := toLeft S
  map := toLeftMap S
  map_id M := by
    apply Mod.hom_ext
    rw [toLeftMap_hom]
    rfl
  map_comp f g := by
    apply Mod.hom_ext
    change (toLeftMap S (f ≫ g)).hom = (toLeftMap S f).hom ≫ (toLeftMap S g).hom
    rw [toLeftMap_hom, toLeftMap_hom, toLeftMap_hom]
    rfl

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable (S : C) [MonObj S] [IsCommMonObj S]

/-- The actual two braidings recover the entire original left action. -/
theorem left_recovery_smul (M : CategoryTheory.Mod C S) :
    ModObj.smul (M := S) (X := (toLeft S (toRight S M)).X) =
      ModObj.smul (M := S) (X := M.X) := by
  rw [toLeft_smul]
  dsimp only [leftAction]
  rw [toRight_smul]
  dsimp only [rightAction]
  change (β_ S M.X).hom ≫ (β_ M.X S).hom ≫ ModObj.smul (M := S) (X := M.X) = _
  rw [SymmetricCategory.symmetry_assoc]

/-- The actual two braidings recover the entire original right action. -/
theorem right_recovery_smul (M : RightModule S) :
    ModObj.smul (M := mop S) (X := (toRight S (toLeft S M)).X) =
      ModObj.smul (M := mop S) (X := M.X) := by
  rw [toRight_smul]
  dsimp only [rightAction]
  rw [toLeft_smul]
  dsimp only [leftAction]
  change (β_ M.X S).hom ≫ (β_ S M.X).hom ≫ ModObj.smul (M := mop S) (X := M.X) = _
  rw [SymmetricCategory.symmetry_assoc]

/-- The whole recovered left module is isomorphic to its original module. -/
def leftRecoveryIso (M : CategoryTheory.Mod C S) : toLeft S (toRight S M) ≅ M where
  hom := Mod.Hom.mk' (𝟙 M.X) (by
    let a : S ⊗ M.X ⟶ M.X := ModObj.smul (M := S) (X := M.X)
    let b : S ⊗ M.X ⟶ M.X :=
      ModObj.smul (M := S) (X := (toLeft S (toRight S M)).X)
    have h : b = a := left_recovery_smul S M
    change b ≫ 𝟙 M.X = (S ◁ 𝟙 M.X) ≫ a
    rw [h, whiskerLeft_id]
    exact (Category.comp_id a).trans (Category.id_comp a).symm)
  inv := Mod.Hom.mk' (𝟙 M.X) (by
    let a : S ⊗ M.X ⟶ M.X := ModObj.smul (M := S) (X := M.X)
    let b : S ⊗ M.X ⟶ M.X :=
      ModObj.smul (M := S) (X := (toLeft S (toRight S M)).X)
    have h : b = a := left_recovery_smul S M
    change a ≫ 𝟙 M.X = (S ◁ 𝟙 M.X) ≫ b
    rw [h, whiskerLeft_id]
    exact (Category.comp_id a).trans (Category.id_comp a).symm)
  hom_inv_id := by
    apply Mod.hom_ext
    change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
    exact Category.id_comp _
  inv_hom_id := by
    apply Mod.hom_ext
    change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
    exact Category.id_comp _

/-- The actual recovery map is the entire original object identity. -/
theorem leftRecoveryIso_hom (M : CategoryTheory.Mod C S) :
    (leftRecoveryIso S M).hom.hom = 𝟙 M.X := rfl

/-- The actual inverse recovery map is the entire original object identity. -/
theorem leftRecoveryIso_inv (M : CategoryTheory.Mod C S) :
    (leftRecoveryIso S M).inv.hom = 𝟙 M.X := rfl

/-- The whole recovered right module is isomorphic to its original module. -/
def rightRecoveryIso (M : RightModule S) : toRight S (toLeft S M) ≅ M where
  hom := Mod.Hom.mk' (𝟙 M.X) (by
    let a : M.X ⊗ S ⟶ M.X := ModObj.smul (M := mop S) (X := M.X)
    let b : M.X ⊗ S ⟶ M.X :=
      ModObj.smul (M := mop S) (X := (toRight S (toLeft S M)).X)
    have h : b = a := right_recovery_smul S M
    change b ≫ 𝟙 M.X = (𝟙 M.X ▷ S) ≫ a
    rw [h, id_whiskerRight]
    exact (Category.comp_id a).trans (Category.id_comp a).symm)
  inv := Mod.Hom.mk' (𝟙 M.X) (by
    let a : M.X ⊗ S ⟶ M.X := ModObj.smul (M := mop S) (X := M.X)
    let b : M.X ⊗ S ⟶ M.X :=
      ModObj.smul (M := mop S) (X := (toRight S (toLeft S M)).X)
    have h : b = a := right_recovery_smul S M
    change a ≫ 𝟙 M.X = (𝟙 M.X ▷ S) ≫ b
    rw [h, id_whiskerRight]
    exact (Category.comp_id a).trans (Category.id_comp a).symm)
  hom_inv_id := by
    apply Mod.hom_ext
    change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
    exact Category.id_comp _
  inv_hom_id := by
    apply Mod.hom_ext
    change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X
    exact Category.id_comp _

/-- The actual right-module recovery map is the original object identity. -/
theorem rightRecoveryIso_hom (M : RightModule S) :
    (rightRecoveryIso S M).hom.hom = 𝟙 M.X := rfl

/-- The actual inverse right-module recovery map is the original object identity. -/
theorem rightRecoveryIso_inv (M : RightModule S) :
    (rightRecoveryIso S M).inv.hom = 𝟙 M.X := rfl

/-- Full naturality under every original left-module morphism. -/
def leftRecoveryNatIso : leftToRight S ⋙ rightToLeft S ≅ 𝟭 (CategoryTheory.Mod C S) :=
  NatIso.ofComponents (leftRecoveryIso S) (by
    intro M N f
    apply Mod.hom_ext
    change (toLeftMap S (toRightMap S f)).hom ≫ (leftRecoveryIso S N).hom.hom =
      (leftRecoveryIso S M).hom.hom ≫ f.hom
    rw [toLeftMap_hom, toRightMap_hom, leftRecoveryIso_hom, leftRecoveryIso_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Full naturality under every original right-module morphism. -/
def rightRecoveryNatIso : rightToLeft S ⋙ leftToRight S ≅ 𝟭 (RightModule S) :=
  NatIso.ofComponents (rightRecoveryIso S) (by
    intro M N f
    apply Mod.hom_ext
    change (toRightMap S (toLeftMap S f)).hom ≫ (rightRecoveryIso S N).hom.hom =
      (rightRecoveryIso S M).hom.hom ≫ f.hom
    rw [toRightMap_hom, toLeftMap_hom, rightRecoveryIso_hom, rightRecoveryIso_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The symmetric conversion is an equivalence with the original unit and counit. -/
def moduleEquivalence : CategoryTheory.Mod C S ≌ RightModule S where
  functor := leftToRight S
  inverse := rightToLeft S
  unitIso := (leftRecoveryNatIso S).symm
  counitIso := rightRecoveryNatIso S
  functor_unitIso_comp M := by
    apply Mod.hom_ext
    change (toRightMap S (leftRecoveryIso S M).inv).hom ≫
      (rightRecoveryIso S (toRight S M)).hom.hom = 𝟙 M.X
    rw [toRightMap_hom, leftRecoveryIso_inv, rightRecoveryIso_hom]
    exact Category.id_comp _

/-- The forward morphism round trip uses the actual right comparison isos. -/
theorem moduleEquivalence_right_map_inverse {M N : RightModule S} (f : M ⟶ N) :
    (leftToRight S).map ((rightToLeft S).map f) =
      (rightRecoveryIso S M).hom ≫ f ≫ (rightRecoveryIso S N).inv :=
  (moduleEquivalence S).fun_inv_map M N f

/-- The inverse morphism round trip uses the actual left comparison isos. -/
theorem moduleEquivalence_left_map_inverse {M N : CategoryTheory.Mod C S} (f : M ⟶ N) :
    (rightToLeft S).map ((leftToRight S).map f) =
      (leftRecoveryIso S M).hom ≫ f ≫ (leftRecoveryIso S N).inv :=
  (moduleEquivalence S).inv_fun_map M N f

/-- The original unit and counit satisfy the full right-module triangle. -/
theorem moduleEquivalence_right_triangle (M : CategoryTheory.Mod C S) :
    (leftToRight S).map ((moduleEquivalence S).unitIso.hom.app M) ≫
      (moduleEquivalence S).counitIso.hom.app ((leftToRight S).obj M) =
      𝟙 ((leftToRight S).obj M) :=
  (moduleEquivalence S).functor_unit_comp M

/-- The original unit and counit satisfy the full left-module triangle. -/
theorem moduleEquivalence_left_triangle (M : RightModule S) :
    (moduleEquivalence S).unitIso.hom.app ((rightToLeft S).obj M) ≫
      (rightToLeft S).map ((moduleEquivalence S).counitIso.hom.app M) =
      𝟙 ((rightToLeft S).obj M) :=
  (moduleEquivalence S).unit_inverse_comp M

end Symmetric

end CategoryTheory.CommutativeModuleConversion
