/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightTensorHom
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorParametrized

/-!
# Source maps and the original right tensor-Hom pairing

Precomposition is transported through the chosen monoidal-opposite Hom.
Its carrier is identified by the original tensor-right adjunction, rather
than by an equality of chosen adjunction data. The balanced pairing
criterion retains both original scalar action maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite BraidedCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.MonoidalOpposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The actual right adjunct of source precomposition is the original ambient pre-map. -/
theorem originalRightTensorAdjunction_pre {X Y : C} (f : X ⟶ Y) (Z : C) :
    (originalRightTensorAdjunction X).homEquiv ((ihom Y).obj Z) Z
      (((ihom Y).obj Z ◁ f) ≫ (originalRightTensorAdjunction Y).counit.app Z) =
        (MonoidalClosed.pre f).app Z := by
  rw [originalRightTensorAdjunction_homEquiv, originalRightTensorAdjunction_counit]
  rw [← braiding_naturality_left_assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalClosed.curry_pre_app]
  have h : MonoidalClosed.curry ((ihom.ev Y).app Z) = 𝟙 ((ihom Y).obj Z) := by
    rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry]
  rw [h, Category.id_comp]

/-- Source precomposition satisfies the actual right evaluation equation on every original map. -/
theorem originalRightTensorAdjunction_pre_evaluation {X Y : C} (f : X ⟶ Y) (Z : C) :
    ((MonoidalClosed.pre f).app Z ▷ X) ≫ (originalRightTensorAdjunction X).counit.app Z =
      (((ihom Y).obj Z) ◁ f) ≫ (originalRightTensorAdjunction Y).counit.app Z := by
  let a := originalRightTensorAdjunction X
  have h := congrArg (a.homEquiv ((ihom Y).obj Z) Z).symm
    (originalRightTensorAdjunction_pre f Z)
  rw [Equiv.symm_apply_apply, a.homEquiv_counit] at h
  exact h.symm

/-- The chosen opposite pre-map keeps the entire original ambient source map. -/
theorem monoidalClosedOpposite_pre {X Y : C} (f : X ⟶ Y) (Z : C) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    ((MonoidalClosed.pre f.mop).app (mop Z)).unmop = (MonoidalClosed.pre f).app Z := by
  let : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
  let H := (ihom Y).obj Z
  let k := f.mop ▷ mop H ≫ (ihom.ev (mop Y)).app (mop Z)
  have hp : MonoidalClosed.curry k = (MonoidalClosed.pre f.mop).app (mop Z) := by
    dsimp only [k]
    rw [← MonoidalClosed.curry_pre_app]
    have h : MonoidalClosed.curry ((ihom.ev (mop Y)).app (mop Z)) = 𝟙 (mop H) := by
      rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry]
      rfl
    rw [h, Category.id_comp]
    rfl
  have hk : k.unmop = (H ◁ f) ≫ (originalRightTensorAdjunction Y).counit.app Z := by
    change (H ◁ f) ≫ ((ihom.ev (mop Y)).app (mop Z)).unmop = _
    rw [monoidalClosedOpposite_counit]
  have h := monoidalClosedOpposite_homEquiv X H Z k.unmop
  change (MonoidalClosed.curry k).unmop =
    (originalRightTensorAdjunction X).homEquiv H Z k.unmop at h
  rw [hp, hk, originalRightTensorAdjunction_pre] at h
  exact h

end CategoryTheory.MonoidalOpposite

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] {A : C} [MonObj A]

/-- The chosen opposite closed structure used to transport contravariant module Hom maps. -/
local instance preMapOppositeClosed : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)

/-- Every original left-module source map gives its actual contravariant right-module Hom map. -/
def rightHomPre {N N' : Mod C A} (f : N ⟶ N') (X : C) :
    (rightHomFunctor N').obj X ⟶ (rightHomFunctor N).obj X :=
  (RightModuleFree.unmopModules A).map (homPre (leftOppositeMap f) (mop X))

/-- The transported source map retains the original ambient internal-Hom precomposition. -/
theorem rightHomPre_carrier {N N' : Mod C A} (f : N ⟶ N') (X : C) :
    (rightHomPre f X).hom = (MonoidalClosed.pre f.hom).app X := by
  change ((MonoidalClosed.pre f.hom.mop).app (mop X)).unmop = _
  exact monoidalClosedOpposite_pre f.hom X

/-- The original left-module source equation proves right scalar linearity of that same pre-map. -/
theorem rightHomPre_linear {N N' : Mod C A} (f : N ⟶ N') (X : C) :
    ((rightHomFunctor N').obj X).mod.smul ≫ (MonoidalClosed.pre f.hom).app X =
      ((MonoidalClosed.pre f.hom).app X ▷ A) ≫ ((rightHomFunctor N).obj X).mod.smul := by
  have h := (rightHomPre f X).isModHom.smul_hom
  rw [rightHomPre_carrier] at h
  exact h

/-- Right currying is scalar linear exactly when the two original balancing words agree. -/
theorem rightCurry_linear_iff (M : RightModuleFree.Carrier A) (N : Mod C A) {X : C}
    (k : M.X ⊗ N.X ⟶ X) :
    M.mod.smul ≫ (originalRightTensorAdjunction N.X).homEquiv M.X X k =
        ((originalRightTensorAdjunction N.X).homEquiv M.X X k ▷ A) ≫
          ((rightHomFunctor N).obj X).mod.smul ↔
      (M.mod.smul ▷ N.X) ≫ k = (α_ M.X A N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ k := by
  let Mo := RightModuleFree.mopModule A M
  let No := leftOpposite N
  let c : mop M.X ⟶ (ihom (mop N.X)).obj (mop X) := MonoidalClosed.curry (A := mop N.X) k.mop
  have hc : c.unmop =
      (originalRightTensorAdjunction N.X).homEquiv M.X X k := by
    exact monoidalClosedOpposite_homEquiv N.X M.X X k
  have h := curry_linear_iff No Mo k.mop
  constructor
  · intro hlin
    have ho : Mo.mod.smul ≫ c =
        (mop A ◁ c) ≫ (homObject No (mop X)).mod.smul := by
      apply Quiver.Hom.unmop_inj
      change M.mod.smul ≫ c.unmop =
        (c.unmop ▷ A) ≫ ((rightHomFunctor N).obj X).mod.smul
      rw [hc]
      exact hlin
    have hb := congrArg Quiver.Hom.unmop (h.mp ho)
    simp only [pointFst_formula, pointSnd_formula, Category.assoc] at hb
    change (α_ M.X A N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ k = (M.mod.smul ▷ N.X) ≫ k at hb
    exact hb.symm
  · intro hbal
    have ho : pointFst No Mo ≫ k.mop = pointSnd No Mo ≫ k.mop := by
      rw [pointFst_formula, pointSnd_formula]
      simp only [Category.assoc]
      apply Quiver.Hom.unmop_inj
      change (α_ M.X A N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ k = (M.mod.smul ▷ N.X) ≫ k
      exact hbal.symm
    have hl := congrArg Quiver.Hom.unmop (h.mpr ho)
    change M.mod.smul ≫ c.unmop =
      (c.unmop ▷ A) ≫ ((rightHomFunctor N).obj X).mod.smul at hl
    rw [hc] at hl
    exact hl

/-- The original right evaluation satisfies the complete source scalar balancing equation. -/
theorem rightEvaluation_balance (N : Mod C A) (X : C) :
    (((rightHomFunctor N).obj X).mod.smul ▷ N.X) ≫
        (originalRightTensorAdjunction N.X).counit.app X =
      (α_ ((ihom N.X).obj X) A N.X).hom ≫
        (((ihom N.X).obj X) ◁ N.mod.smul) ≫
          (originalRightTensorAdjunction N.X).counit.app X := by
  let a := originalRightTensorAdjunction N.X
  let M := (rightHomFunctor N).obj X
  have h : a.homEquiv M.X X (a.counit.app X) = 𝟙 M.X := by
    change a.homEquiv ((ihom N.X).obj X) X (a.counit.app X) = 𝟙 ((ihom N.X).obj X)
    rw [← a.homEquiv_symm_id X]
    exact Equiv.apply_symm_apply _ _
  apply (rightCurry_linear_iff M N (a.counit.app X)).mp
  erw [h]
  simp only [Category.comp_id, id_whiskerRight, Category.id_comp]

end CategoryTheory.Mod.RightLeftTensor
