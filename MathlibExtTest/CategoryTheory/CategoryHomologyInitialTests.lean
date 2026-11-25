/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Initial

/-! # Tests for morphism-inverting category-homology coefficients -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyInitialTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)
  [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]

example (i : C) (hi : IsInitial i) :
    (Functor.const C).obj (M.obj i) ≅ M :=
  CategoryHomology.constIsoOfIsInitial M i hi

example [Abelian A] (i : C) (hi : IsInitial i) (n : ℕ) :
    CategoryHomology.homologyWithCoefficients
        ((Functor.const C).obj (M.obj i)) n ≅
      CategoryHomology.homologyWithCoefficients M n :=
  CategoryHomology.homologyWithCoefficientsIsoConstOfIsInitial M i hi n

end CategoryTheory.CategoryHomologyInitialTests

end
