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

import MathlibExt.CategoryTheory.ExactCategory.Biproduct

/-!
# Consumer checks for biproduct closure of admissible exact sequences

Pins the component maps of `ExactCategory.biprodShortComplex` and checks
admissibility of the biproduct of two generic admissible exact complexes via
`ExactCategory.isAdmissibleExact_biprod`.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MathlibExtTest.CategoryTheory.ExactCategory.BiproductTests

section Computation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

example (S T : ShortComplex C) :
    (ExactCategory.biprodShortComplex S T).f = biprod.map S.f T.f :=
  ExactCategory.biprodShortComplex_f S T

example (S T : ShortComplex C) :
    (ExactCategory.biprodShortComplex S T).g = biprod.map S.g T.g :=
  ExactCategory.biprodShortComplex_g S T

example (S T : ShortComplex C) :
    (ExactCategory.biprodShortComplex S T).X₁ = (S.X₁ ⊞ T.X₁) :=
  rfl

example (S T : ShortComplex C) :
    (ExactCategory.biprodShortComplex S T).X₂ = (S.X₂ ⊞ T.X₂) :=
  rfl

example (S T : ShortComplex C) :
    (ExactCategory.biprodShortComplex S T).X₃ = (S.X₃ ⊞ T.X₃) :=
  rfl

end Computation

section Admissible

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example {S T : ShortComplex C} (hS : ExactCategory.IsAdmissibleExact S)
    (hT : ExactCategory.IsAdmissibleExact T) :
    ExactCategory.IsAdmissibleExact (ExactCategory.biprodShortComplex S T) :=
  ExactCategory.isAdmissibleExact_biprod hS hT

end Admissible

end MathlibExtTest.CategoryTheory.ExactCategory.BiproductTests
