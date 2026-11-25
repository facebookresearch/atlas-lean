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
# Consumer checks for exact paired functors

Inference for the paired exact-functor instance and one
mapped-admissible-sequence check through the public exact-functor API.

Nonclaims: no two-source product (`Functor.prod`), diagonal (`Functor.diag`), or
biproduct-functor exactness; no Waldhausen additivity; no K-theory or G-theory;
no realization; no spectra; no Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace MathlibExtTest.CategoryTheory.Products.FunctorProdExactTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (A : Type u₃) [Category.{v₃} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [ExactCategory A]

variable (F : A ⥤ C) (G : A ⥤ D) [F.Additive] [G.Additive]
  [F.IsExact] [G.IsExact]

example : (F.prod' G).IsExact := inferInstance

example (S : ShortComplex A) (hS : ExactCategory.IsAdmissibleExact S) :
    ExactCategory.IsAdmissibleExact (S.map (F.prod' G)) :=
  (F.prod' G).map_admissibleExact S hS

end MathlibExtTest.CategoryTheory.Products.FunctorProdExactTests
