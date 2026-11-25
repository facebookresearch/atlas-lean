/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality

/-! # Tests for coefficient category-bar functoriality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarFunctorialityTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  {M N : CategoryTheory.Functor C A}

example (α : M ⟶ N) :
    CategoryHomology.coefficientBarSimplicial M ⟶
      CategoryHomology.coefficientBarSimplicial N :=
  CategoryHomology.coefficientBarSimplicialMap α

example : (C ⥤ A) ⥤ SimplicialObject A :=
  CategoryHomology.coefficientBarSimplicialFunctor

example [Abelian A] : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  CategoryHomology.normalizedCoefficientBarComplexFunctor

example [Abelian A] (n : ℕ) : (C ⥤ A) ⥤ A :=
  CategoryHomology.homologyWithCoefficientsFunctor n

end CategoryTheory.CategoryHomologyBarFunctorialityTests

end
