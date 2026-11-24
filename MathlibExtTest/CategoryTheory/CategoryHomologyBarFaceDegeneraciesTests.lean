/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFaceDegeneracies

/-! # Tests for mixed coefficient category-bar identities -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarFaceDegeneraciesTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    CategoryHomology.coefficientBarDegeneracy M j.succ ≫
        CategoryHomology.coefficientBarFace M i.castSucc =
      CategoryHomology.coefficientBarFace M i ≫
        CategoryHomology.coefficientBarDegeneracy M j :=
  CategoryHomology.coefficientBar_face_degeneracy_of_le M i j hij

example {n : ℕ} (i : Fin (n + 1)) :
    CategoryHomology.coefficientBarDegeneracy M i ≫
        CategoryHomology.coefficientBarFace M i.castSucc = 𝟙 _ :=
  CategoryHomology.coefficientBar_face_degeneracy_self M i

example {n : ℕ} (i : Fin (n + 1)) :
    CategoryHomology.coefficientBarDegeneracy M i ≫
        CategoryHomology.coefficientBarFace M i.succ = 𝟙 _ :=
  CategoryHomology.coefficientBar_face_degeneracy_succ M i

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    CategoryHomology.coefficientBarDegeneracy M j.castSucc ≫
        CategoryHomology.coefficientBarFace M i.succ =
      CategoryHomology.coefficientBarFace M i ≫
        CategoryHomology.coefficientBarDegeneracy M j :=
  CategoryHomology.coefficientBar_face_degeneracy_of_gt M i j hji

end CategoryTheory.CategoryHomologyBarFaceDegeneraciesTests

end
