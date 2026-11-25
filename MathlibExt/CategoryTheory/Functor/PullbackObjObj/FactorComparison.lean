/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Base change for a mapping corner along a given factor

For a supplied factor law `j ≫ r = σ`, Mathlib's `mapArrowLeft` applied to
`(𝟙 A, r) : Arrow.mk j ⟶ Arrow.mk σ` compares the two chosen corners.
Its target component is a base change of restriction along `r`.
-/

public section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.PullbackObjObj.FactorComparison

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)
  {A M B : C₁} {X Y : C₃}
  (j : A ⟶ M) (r : M ⟶ B) (σ : A ⟶ B) (fac : j ≫ r = σ)
  (p : X ⟶ Y)
  (cornerσ : G.PullbackObjObj σ p) (cornerj : G.PullbackObjObj j p)

include fac

/-- The target component of the native comparison is a pullback of restriction
along `r` against the second projection of the supplied `j` corner. -/
theorem targetMap_isPullback :
    IsPullback cornerσ.snd
      (mapArrowLeft (f₁ := Arrow.mk σ) (f₁' := Arrow.mk j) (f₃ := Arrow.mk p)
        cornerσ cornerj (Arrow.homMk (𝟙 A) r ((Category.id_comp σ).trans fac.symm))).right
      ((G.map r.op).app Y) cornerj.snd := by
  let sq : Arrow.mk j ⟶ Arrow.mk σ :=
    Arrow.homMk (𝟙 A) r ((Category.id_comp σ).trans fac.symm)
  let m := mapArrowLeft (f₃ := Arrow.mk p) cornerσ cornerj sq
  change IsPullback cornerσ.snd m.right ((G.map r.op).app Y) cornerj.snd
  have hfst : m.right ≫ cornerj.fst = cornerσ.fst := by
    simp [m, sq, mapArrowLeft_right]
  have hsnd : m.right ≫ cornerj.snd = cornerσ.snd ≫ (G.map r.op).app Y := by
    simp [m, sq, mapArrowLeft_right]
  refine IsPullback.of_bot ?_ hsnd.symm cornerj.isPullback.flip
  rw [hfst, ← NatTrans.comp_app, ← G.map_comp, ← op_comp, fac]
  exact cornerσ.isPullback.flip

end CategoryTheory.Functor.PullbackObjObj.FactorComparison
