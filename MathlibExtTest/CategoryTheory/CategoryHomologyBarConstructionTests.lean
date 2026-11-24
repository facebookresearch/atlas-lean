/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarConstruction

/-! # Tests for the category-homology coefficient bar -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarConstructionTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

example (n : ℕ) : A :=
  CategoryHomology.coefficientBarObj M n

example {n : ℕ} (i : Fin (n + 2)) :
    CategoryHomology.coefficientBarObj M (n + 1) ⟶
      CategoryHomology.coefficientBarObj M n :=
  CategoryHomology.coefficientBarFace M i

example {n : ℕ} (i : Fin (n + 1)) :
    CategoryHomology.coefficientBarObj M n ⟶
      CategoryHomology.coefficientBarObj M (n + 1) :=
  CategoryHomology.coefficientBarDegeneracy M i

example {n : ℕ} (F : ComposableArrows C (n + 1)) :
    CategoryHomology.coefficientBarι M F ≫
        CategoryHomology.coefficientBarFace M (0 : Fin (n + 2)) =
      M.map (F.map' 0 1) ≫
        CategoryHomology.coefficientBarι M ((nerve C).δ 0 F) :=
  CategoryHomology.coefficientBarι_face_zero M F

end CategoryTheory.CategoryHomologyBarConstructionTests

end
