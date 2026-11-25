/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Functor.PullbackObjObj.FactorComparison
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Weakness of the whole corner along a given factor

The actual target comparison is the supplied corner's pullback of
the original target restriction. Right properness and the two original
weak source restrictions transfer the original first-factor corner's
weakness to the whole original composite corner.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomotopicalAlgebra.MappingCornerFactorWeak

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [ModelCategory C₂] [IsRightProper C₂]

/-- The full weak comparison retains the supplied factor equation,
both original strict corners, and both actual source restrictions. -/
theorem weak_of_factor
    (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)
    {A M B : C₁} {X Y : C₃}
    (j : A ⟶ M) (r : M ⟶ B) (σ : A ⟶ B) (fac : j ≫ r = σ) (p : X ⟶ Y)
    (cornerσ : G.PullbackObjObj σ p) (cornerj : G.PullbackObjObj j p)
    (hX : weakEquivalences C₂ ((G.map r.op).app X))
    (hY : weakEquivalences C₂ ((G.map r.op).app Y))
    (hpost : fibrations C₂ ((G.obj (op A)).map p))
    (hcorner : weakEquivalences C₂ cornerj.π) :
    weakEquivalences C₂ cornerσ.π := by
  let m := Functor.PullbackObjObj.mapArrowLeft (f₁ := Arrow.mk σ) (f₁' := Arrow.mk j)
    (f₃ := Arrow.mk p) cornerσ cornerj
    (Arrow.homMk (𝟙 A) r ((Category.id_comp σ).trans fac.symm))
  let t := m.right
  have hsecond : fibrations C₂ cornerj.snd :=
    MorphismProperty.of_isPullback cornerj.isPullback hpost
  have hRightProper : IsRightProper C₂ := inferInstance
  have hProper := hRightProper.weakEquivalences_isStableUnderBaseChangeAgainst_fibrations
  have ht : weakEquivalences C₂ t :=
    (hProper.isStableUnderBaseChangeAlong cornerj.snd hsecond).of_isPullback
      (Functor.PullbackObjObj.FactorComparison.targetMap_isPullback
        G j r σ fac p cornerσ cornerj) hY
  apply (weakEquivalences C₂).of_postcomp cornerσ.π t ht
  have hfac : cornerσ.π ≫ t = (G.map r.op).app X ≫ cornerj.π := by
    exact m.w.symm
  rw [hfac]
  exact (weakEquivalences C₂).comp_mem _ _ hX hcorner

end HomotopicalAlgebra.MappingCornerFactorWeak
