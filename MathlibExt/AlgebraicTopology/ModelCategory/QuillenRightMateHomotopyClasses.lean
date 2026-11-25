/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenHomotopyAdjunction
import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate

/-!
# Genuine original right-mate homotopy-class comparison

Actual Quillen transposition and the canonical original mate equation
compare postcomposition with the SAME right mate to precomposition with
the original left comparison. A genuine weak left comparison between
actual cofibrant images therefore gives bijections on original model
homotopy classes. No weak right mate or derived adjunction is assumed.
-/

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.RightHomotopyClass

/-- Original postcomposition on right classes, through the canonical left/right class equivalence at
actual
cofibrant/fibrant endpoints. -/
def postcompOfCofibrant {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {X Y Z : C} [IsCofibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : RightHomotopyClass X Y) (g : Y ⟶ Z) : RightHomotopyClass X Z :=
  leftHomotopyClassEquivRightHomotopyClass
    ((leftHomotopyClassEquivRightHomotopyClass.symm f).postcomp g)

/-- Every original representative retains exactly its original postcomposition map. -/
theorem postcompOfCofibrant_mk {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {X Y Z : C} [IsCofibrant X] [IsFibrant Y] [IsFibrant Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RightHomotopyClass.mk f).postcompOfCofibrant g = RightHomotopyClass.mk (f ≫ g) := rfl

end HomotopicalAlgebra.RightHomotopyClass

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [IsQuillenAdjunction adj₁] [IsQuillenAdjunction adj₂]

/-- Postcomposition by the original right mate on actual right classes, with target fibrancy
supplied by the two
original Quillen adjunctions. -/
def rightMatePostcompRightHomotopyClass (α : L₁ ⟶ L₂)
    (K : C) (F : D) [IsCofibrant K] [IsFibrant F] :
    RightHomotopyClass K (R₂.obj F) → RightHomotopyClass K (R₁.obj F) := by
  let _ : IsFibrant (R₁.obj F) := preservesFibrantObjects (adj := adj₁) inferInstance
  let _ : IsFibrant (R₂.obj F) := preservesFibrantObjects (adj := adj₂) inferInstance
  exact fun f => f.postcompOfCofibrant ((conjugateEquiv adj₂ adj₁ α).app F)

include adj₁ adj₂ in
/-- A genuine original weak left comparison gives bijective postcomposition by the SAME canonical
right mate on actual
model classes. -/
theorem rightMate_postcomp_rightHomotopyClass_bijective (α : L₁ ⟶ L₂)
    (hα : ∀ (X : C) [IsCofibrant X], WeakEquivalence (α.app X))
    (K : C) (F : D) [IsCofibrant K] [IsFibrant F] :
    Function.Bijective (rightMatePostcompRightHomotopyClass adj₁ adj₂ α K F) := by
  let _ : IsCofibrant (L₁.obj K) := preservesCofibrantObjects (adj := adj₁) inferInstance
  let _ : IsCofibrant (L₂.obj K) := preservesCofibrantObjects (adj := adj₂) inferInstance
  let _ : IsFibrant (R₁.obj F) := preservesFibrantObjects (adj := adj₁) inferInstance
  let _ : IsFibrant (R₂.obj F) := preservesFibrantObjects (adj := adj₂) inferInstance
  let _ : WeakEquivalence (α.app K) := hα K
  let E₁ := rightHomotopyHomEquiv (adj := adj₁) K F
  let E₂ := rightHomotopyHomEquiv (adj := adj₂) K F
  let β := (conjugateEquiv adj₂ adj₁ α).app F
  have hnat (φ : RightHomotopyClass (L₂.obj K) F) :
      E₁ (φ.precomp (α.app K)) = (E₂ φ).postcompOfCofibrant β := by
    induction φ using Quot.inductionOn with
    | _ f =>
      change RightHomotopyClass.mk (adj₁.homEquiv K F (α.app K ≫ f)) =
        RightHomotopyClass.mk (adj₂.homEquiv K F f ≫ β)
      exact congrArg RightHomotopyClass.mk (Adjunction.homEquiv_comp_conjugateEquiv adj₁ adj₂ α f)
  have hpre := RightHomotopyClass.precomp_bijective_of_weakEquivalence F (α.app K)
  constructor
  · intro x y h
    have hx : E₁ ((E₂.symm x).precomp (α.app K)) = x.postcompOfCofibrant β := by
      simpa only [Equiv.apply_symm_apply] using hnat (E₂.symm x)
    have hy : E₁ ((E₂.symm y).precomp (α.app K)) = y.postcompOfCofibrant β := by
      simpa only [Equiv.apply_symm_apply] using hnat (E₂.symm y)
    exact E₂.symm.injective (hpre.injective (E₁.injective (hx.trans (h.trans hy.symm))))
  · intro y
    obtain ⟨a, ha⟩ := hpre.surjective (E₁.symm y)
    exact ⟨E₂ a, (hnat a).symm.trans ((congrArg E₁ ha).trans (E₁.apply_symm_apply y))⟩

end CategoryTheory.Adjunction.IsQuillenAdjunction
