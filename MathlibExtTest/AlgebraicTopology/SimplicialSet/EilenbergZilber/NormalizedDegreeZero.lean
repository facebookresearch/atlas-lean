/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.DoldKan Simplicial

universe w v u

namespace SSet.EilenbergZilberTests

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C)

/-- In degree zero, normalization followed by inclusion fixes every simplex
generator: there are no degenerate zero-simplices to remove. -/
theorem degreeZero_normalization_generator (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f 0 ≫
        (X.fromNormalizedChainComplex R).f 0 =
      X.ιChainComplex x := by
  rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f,
    PInfty_f_0]
  exact Category.comp_id _

/-- The normalized inclusion/projection round trip fixes every normalized
degree-zero generator. -/
theorem degreeZero_normalized_generator_roundtrip (x : X _⦋0⦌) :
    X.ιNormalizedChainComplex x ≫
        (X.fromNormalizedChainComplex R).f 0 ≫
        (X.toNormalizedChainComplex R).f 0 =
      X.ιNormalizedChainComplex x := by
  rw [fromNormalizedChainComplex_f_toNormalizedChainComplex_f,
    Category.comp_id]

end SSet.EilenbergZilberTests
