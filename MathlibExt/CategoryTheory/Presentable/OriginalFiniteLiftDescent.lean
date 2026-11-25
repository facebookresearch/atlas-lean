/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# A full original finite lift descends through an original filtered cocone

Both finite source objects and the SAME original whole ambient lift are
retained. Actual finite presentability supplies a factor and then its
exact original boundary equality at a common later stage. No model,
weak-equivalence or desired lifting outcome is assumed.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.Limits.OriginalFiniteLiftDescent
variable {C : Type u} [Category.{v} C] {J : Type w} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  {A B : C} [IsFinitelyPresentable.{w} A] [IsFinitelyPresentable.{w} B]
  (i : A ⟶ B) (j : J) (top : A ⟶ F.obj j) (ambient : B ⟶ c.pt)
  (h : i ≫ ambient = top ≫ c.ι.app j)

include hc h

/-- The SAME whole original ambient lift descends to an actual later original stage with its full
boundary equality. -/
theorem exists_lift : ∃ (k : J) (u : j ⟶ k) (l : B ⟶ F.obj k),
    i ≫ l = top ≫ F.map u ∧ l ≫ c.ι.app k = ambient := by
  obtain ⟨k₀, l₀, hl₀⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc ambient
  have he : (i ≫ l₀) ≫ c.ι.app k₀ = top ≫ c.ι.app j :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => i ≫ q) hl₀).trans h)
  obtain ⟨k, v, u, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc (i ≫ l₀) top he
  refine ⟨k, u, l₀ ≫ F.map v, (Category.assoc _ _ _).symm.trans huv, ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => l₀ ≫ q) (c.w v)).trans hl₀)

end CategoryTheory.Limits.OriginalFiniteLiftDescent
