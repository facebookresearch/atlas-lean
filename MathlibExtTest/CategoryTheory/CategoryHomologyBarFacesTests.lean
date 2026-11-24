/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFaces

/-! # Tests for coefficient category-bar face identities -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarFacesTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    CategoryHomology.coefficientBarFace M j.succ ≫
        CategoryHomology.coefficientBarFace M i =
      CategoryHomology.coefficientBarFace M i.castSucc ≫
        CategoryHomology.coefficientBarFace M j :=
  CategoryHomology.coefficientBarFace_comp_face M i j hij

end CategoryTheory.CategoryHomologyBarFacesTests

end
