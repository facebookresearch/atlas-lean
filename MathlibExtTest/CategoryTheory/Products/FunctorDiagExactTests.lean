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
# Consumer checks for exact diagonal functor

Inference for the diagonal exact-functor instance and one
mapped-admissible-sequence check through the public exact-functor API.

Nonclaims: no two-source product (`Functor.prod`) or
biproduct-functor exactness; no Waldhausen additivity; no K-theory or G-theory;
no realization; no spectra; no Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ u₁

namespace MathlibExtTest.CategoryTheory.Products.FunctorDiagExactTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example : (Functor.diag C).IsExact := inferInstance

example (S : ShortComplex C) (hS : ExactCategory.IsAdmissibleExact S) :
    ExactCategory.IsAdmissibleExact (S.map (Functor.diag C)) :=
  Functor.map_admissibleExact (Functor.diag C) S hS

end MathlibExtTest.CategoryTheory.Products.FunctorDiagExactTests
