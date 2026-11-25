/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module


public import MathlibExt.Algebra.Homology.ShortComplex.SplittingComp

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y Z Z₁ Z₂ : C}
variable {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
variable {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
variable [HasBinaryBiproduct Z₁ Z₂]
variable (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
  (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting)

example : (f₁ ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂ = 0 :=
  compLeft_zero (w₁ := w₁) s₂

example :
    (ShortComplex.mk (f₁ ≫ f₂) (biprod.lift (s₂.r ≫ g₁) g₂)
      (compLeft_zero (w₁ := w₁) s₂)).Splitting :=
  compLeft s₁ s₂

example : (compLeft s₁ s₂).r = s₂.r ≫ s₁.r := by
  simp

example : (compLeft s₁ s₂).s =
    biprod.desc (s₁.s ≫ f₂) s₂.s := by
  simp

example : CokernelCofork (f₁ ≫ f₂) :=
  compLeftCokernelCofork (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂

example : (compLeftCokernelCofork
    (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂).π =
    biprod.lift (s₂.r ≫ g₁) g₂ :=
  compLeftCokernelCofork_π
    (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂

example : IsColimit (compLeftCokernelCofork
    (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂) :=
  compLeftCokernelCoforkIsColimit s₁ s₂

end CategoryTheory.ShortComplex.Splitting

end
