/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorParametrized
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorFree
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
The whole actual relative Leibniz Arrow on a free left-module generator is
the original base pushout-product Arrow. All four quotient reductions and
both original coefficient/generator maps enter the comparison.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalCategory

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

/-- The whole original free-generator reduction identifies both corner objects and all attaching maps. -/
def relativeFreePushoutProductIso {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    {K L : C} (i : K ⟶ L) :
    ((relativePushoutProduct (A := A)).obj (Arrow.mk f)).obj (Arrow.mk ((Mod.free A).map i)) ≅
      (Arrow.mk f.hom □ Arrow.mk i) := by
  let R := Functor.PushoutObjObj.ofHasPushout (tensorCurried (A := A)) f ((Mod.free A).map i)
  let S := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f.hom i
  let e₀ := freeTensorIso N K
  let e₁ := freeTensorIso N' K
  let e₂ := freeTensorIso N L
  let e₃ := freeTensorIso N' L
  have hf : ((tensorCurried (A := A)).map f).app ((Mod.free A).obj K) ≫ e₁.hom =
      e₀.hom ≫ ((curriedTensor C).map f.hom).app K :=
    freeTensorIso_coefficient_naturality f K
  have hi : ((tensorCurried (A := A)).obj N).map ((Mod.free A).map i) ≫ e₂.hom =
      e₀.hom ≫ ((curriedTensor C).obj N.X).map i :=
    (freeTensorNatIso N).hom.naturality i
  have raw : IsPushout
      (((tensorCurried (A := A)).map f).app ((Mod.free A).obj K))
      (((tensorCurried (A := A)).obj N).map ((Mod.free A).map i))
      (e₁.hom ≫ S.inl) (e₂.hom ≫ S.inr) :=
    S.isPushout.of_iso' e₀ e₁ e₂ (Iso.refl S.pt) hf.symm hi.symm
      (by simp only [Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.comp_id])
  let eDom := R.isPushout.isoIsPushout _ _ raw
  have hDom₁ : R.inl ≫ eDom.hom = e₁.hom ≫ S.inl := R.isPushout.inl_isoIsPushout_hom _ _ raw
  have hDom₂ : R.inr ≫ eDom.hom = e₂.hom ≫ S.inr := R.isPushout.inr_isoIsPushout_hom _ _ raw
  have hCorner : eDom.hom ≫ S.ι = R.ι ≫ e₃.hom := by
    apply R.isPushout.hom_ext
    · rw [← Category.assoc, hDom₁, Category.assoc, S.inl_ι,
        ← Category.assoc, R.inl_ι]
      exact ((freeTensorNatIso N').hom.naturality i).symm
    · rw [← Category.assoc, hDom₂, Category.assoc, S.inr_ι,
        ← Category.assoc, R.inr_ι]
      exact (freeTensorIso_coefficient_naturality f L).symm
  exact Arrow.isoMk eDom e₃ hCorner

end CategoryTheory.Mod.RightLeftTensor
