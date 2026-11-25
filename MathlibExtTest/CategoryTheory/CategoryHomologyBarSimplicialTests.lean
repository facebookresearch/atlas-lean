/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarSimplicial

/-! # Tests for the simplicial coefficient category bar -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBarSimplicialTests

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

example : SimplicialObject A :=
  CategoryHomology.coefficientBarSimplicial M

example [Preadditive A] : ChainComplex A ℕ :=
  CategoryHomology.coefficientBarComplex M

example [Abelian A] : ChainComplex A ℕ :=
  CategoryHomology.normalizedCoefficientBarComplex M

example [Abelian A] (n : ℕ) : A :=
  CategoryHomology.homologyWithCoefficients M n

end CategoryTheory.CategoryHomologyBarSimplicialTests

end
