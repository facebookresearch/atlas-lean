/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Changing the carrier universe of Ext

The comparison represents the same morphism in a derived category.
It preserves Yoneda composition, short exact extension classes and
injective-resolution representatives. The category and both Ext carrier
universes are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe wD w₁ w₂ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w₁} C] [HasExt.{w₂} C] [HasDerivedCategory.{wD} C]

namespace Abelian.Ext

/-- Change the carrier universe through the same derived morphism. -/
def sizeEquiv (X Y : C) (n : ℕ) : Ext.{w₁} X Y n ≃+ Ext.{w₂} X Y n :=
  (homAddEquiv.{wD, w₁, v, u} (X := X) (Y := Y) (n := n)).trans
    (homAddEquiv.{wD, w₂, v, u} (X := X) (Y := Y) (n := n)).symm

/-- The size comparison preserves the morphism in the common derived category. -/
theorem sizeEquiv_hom {X Y : C} {n : ℕ} (x : Ext.{w₁} X Y n) :
    (sizeEquiv.{wD, w₁, w₂, v, u} X Y n x).hom = x.hom :=
  (homAddEquiv.{wD, w₂, v, u}).apply_symm_apply _

/-- The size comparison preserves the Yoneda composition in every pair of degrees. -/
theorem sizeEquiv_comp {X Y Z : C} {a b c : ℕ}
    (x : Ext.{w₁} X Y a) (y : Ext.{w₁} Y Z b) (h : a + b = c) :
    sizeEquiv.{wD, w₁, w₂, v, u} X Z c (x.comp y h) =
      (sizeEquiv.{wD, w₁, w₂, v, u} X Y a x).comp
        (sizeEquiv.{wD, w₁, w₂, v, u} Y Z b y) h := by
  apply (homAddEquiv.{wD, w₂, v, u}).injective
  simp only [homAddEquiv_apply, sizeEquiv_hom.{wD, w₁, w₂, v, u}, comp_hom]

/-- The extension class is independent of the carrier universe of Ext. -/
theorem sizeEquiv_extClass {S : ShortComplex C} (hS : S.ShortExact) :
    sizeEquiv.{wD, w₁, w₂, v, u} S.X₃ S.X₁ 1
        (ShortComplex.ShortExact.extClass.{w₁, v, u} hS) =
      ShortComplex.ShortExact.extClass.{w₂, v, u} hS := by
  apply (homAddEquiv.{wD, w₂, v, u}).injective
  simp only [homAddEquiv_apply, sizeEquiv_hom.{wD, w₁, w₂, v, u},
    ShortComplex.ShortExact.extClass_hom]

/-- The same covariant extension-class boundary is preserved by size transport. -/
theorem sizeEquiv_comp_extClass {S : ShortComplex C} (hS : S.ShortExact)
    {X : C} {n : ℕ} (x : Ext.{w₁} X S.X₃ n) :
    sizeEquiv.{wD, w₁, w₂, v, u} X S.X₁ (n + 1)
        (x.comp (ShortComplex.ShortExact.extClass.{w₁, v, u} hS) rfl) =
      (sizeEquiv.{wD, w₁, w₂, v, u} X S.X₃ n x).comp
        (ShortComplex.ShortExact.extClass.{w₂, v, u} hS) rfl := by
  rw [sizeEquiv_comp.{wD, w₁, w₂, v, u}, sizeEquiv_extClass.{wD, w₁, w₂, v, u}]

/-- Degree-zero transport preserves the morphism in the abelian category. -/
theorem sizeEquiv_mk₀ {X Y : C} (f : X ⟶ Y) :
    sizeEquiv.{wD, w₁, w₂, v, u} X Y 0 (mk₀.{w₁, v, u} f) =
      mk₀.{w₂, v, u} f := by
  apply (homAddEquiv.{wD, w₂, v, u}).injective
  simp only [homAddEquiv_apply, sizeEquiv_hom.{wD, w₁, w₂, v, u}, mk₀_hom]

end Abelian.Ext

namespace InjectiveResolution

/-- Every representative in the same injective resolution is unchanged by Ext
carrier transport. The resolution is supplied as data; no functorial choice is assumed. -/
theorem extMk_sizeEquiv {X Y : C} (R : InjectiveResolution Y) {n : ℕ}
    (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Abelian.Ext.sizeEquiv.{wD, w₁, w₂, v, u} X Y n (R.extMk.{w₁, v, u} f m hm hf) =
      R.extMk.{w₂, v, u} f m hm hf := by
  apply (Abelian.Ext.homAddEquiv.{wD, w₂, v, u}).injective
  simp only [Abelian.Ext.homAddEquiv_apply,
    Abelian.Ext.sizeEquiv_hom.{wD, w₁, w₂, v, u}, extMk_hom]

end InjectiveResolution

end CategoryTheory
