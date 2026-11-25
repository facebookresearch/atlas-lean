/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarDegeneracies

/-! # Tests for coefficient category-bar degeneracy identities -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarDegeneraciesTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    CategoryHomology.coefficientBarDegeneracy M j ≫
        CategoryHomology.coefficientBarDegeneracy M i.castSucc =
      CategoryHomology.coefficientBarDegeneracy M i ≫
        CategoryHomology.coefficientBarDegeneracy M j.succ :=
  CategoryHomology.coefficientBarDegeneracy_comp_degeneracy M i j hij

end CategoryTheory.CategoryHomologyBarDegeneraciesTests

end
