/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Constant

/-! # Tests for the constant coefficient category bar -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyConstantTests

variable (C : Type u₁) [Category.{v₁} C]
  (A : Type u₂) [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]

example (R : A) :
    CategoryHomology.coefficientBarSimplicial ((Functor.const C).obj R) ≅
      (nerve C ⋙
        ((sigmaConst : A ⥤ (Type (max u₁ v₁) ⥤ A)).obj R)) :=
  CategoryHomology.constantCoefficientBarSimplicialIso C A R

example [Preadditive A] (R : A) :
    CategoryHomology.coefficientBarComplex ((Functor.const C).obj R) ≅
      (nerve C).chainComplex R :=
  CategoryHomology.constantCoefficientBarComplexIso C A R

example [Abelian A] (R : A) (n : ℕ) :
    CategoryHomology.homologyWithCoefficients
        ((Functor.const C).obj R) n ≅
      (nerve C).homology R n :=
  CategoryHomology.homologyWithConstantCoefficientsIso C A R n

end CategoryTheory.CategoryHomologyConstantTests

end
