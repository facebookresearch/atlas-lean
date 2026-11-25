/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Products.Exact

/-!
# Consumer checks for product exact structure

Componentwise admissible-exact behavior, exact-category inference,
one split exact example, and one admissible-mono check for `C × D`.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Products.ExactTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

noncomputable example : ExactCategory (C × D) := inferInstance

example (S : ShortComplex (C × D)) :
    ExactCategory.IsAdmissibleExact S ↔
      ExactCategory.IsAdmissibleExact
        (S.map (CategoryTheory.Prod.fst C D)) ∧
        ExactCategory.IsAdmissibleExact
          (S.map (CategoryTheory.Prod.snd C D)) :=
  prod_isAdmissibleExact_iff C D S

example (X Y : C × D) :
    ExactCategory.IsAdmissibleExact
      (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd
        (by simp)) :=
  ExactCategory.isAdmissibleExact_split X Y

example (X : C × D) : ExactCategory.IsAdmissibleMono (𝟙 X) :=
  ExactCategory.IsAdmissibleMono.id X

end MathlibExtTest.CategoryTheory.Products.ExactTests
