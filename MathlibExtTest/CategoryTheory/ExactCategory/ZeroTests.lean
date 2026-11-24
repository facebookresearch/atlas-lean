/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

import MathlibExt.CategoryTheory.ExactCategory.Zero

/-!
# Zero-leg admissible exactness tests

Focused public-API checks for literal zero/identity admissible exact
sequences and for invertibility of either remaining map when the other
endpoint is zero.  Neither result assumes `Balanced`.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.CategoryTheory.ExactCategory.ZeroTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example {Z B : C} (hZ : IsZero Z) :
    IsAdmissibleExact
      (ShortComplex.mk (0 : Z ⟶ B) (𝟙 B) (by simp)) :=
  isAdmissibleExact_zero_id hZ

example {A Z : C} (hZ : IsZero Z) :
    IsAdmissibleExact
      (ShortComplex.mk (𝟙 A) (0 : A ⟶ Z) (by simp)) :=
  isAdmissibleExact_id_zero hZ

example {S : ShortComplex C} (hS : IsAdmissibleExact S)
    (hX₁ : IsZero S.X₁) : IsIso S.g :=
  isIso_g_of_isAdmissibleExact_of_isZero hS hX₁

example {S : ShortComplex C} (hS : IsAdmissibleExact S)
    (hX₃ : IsZero S.X₃) : IsIso S.f :=
  isIso_f_of_isAdmissibleExact_of_isZero hS hX₃

end MathlibExtTest.CategoryTheory.ExactCategory.ZeroTests
