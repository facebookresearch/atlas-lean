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

import MathlibExt.CategoryTheory.Products.FunctorExact

/-!
# Consumer checks for exact product projections

Inference for the two projection exact instances and one
mapped-admissible-sequence check through the public exact-functor API.

Nonclaims: no pairing (`Functor.prod'`), product, diagonal (`Functor.diag`), or
biproduct-functor exactness; no Waldhausen additivity; no K-theory or G-theory;
no realization; no spectra; no Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Products.FunctorExactTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

example : (CategoryTheory.Prod.fst C D).IsExact := inferInstance

example : (CategoryTheory.Prod.snd C D).IsExact := inferInstance

example (S : ShortComplex (C × D)) (hS : ExactCategory.IsAdmissibleExact S) :
    ExactCategory.IsAdmissibleExact (S.map (CategoryTheory.Prod.fst C D)) ∧
      ExactCategory.IsAdmissibleExact (S.map (CategoryTheory.Prod.snd C D)) :=
  ⟨(CategoryTheory.Prod.fst C D).map_admissibleExact S hS,
    (CategoryTheory.Prod.snd C D).map_admissibleExact S hS⟩

end MathlibExtTest.CategoryTheory.Products.FunctorExactTests
