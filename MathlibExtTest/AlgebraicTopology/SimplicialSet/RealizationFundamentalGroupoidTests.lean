/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoid

/-!
# Realization fundamental-groupoid tests

These tests pin the realization functor, its vertex and edge representatives,
the composition orientation, and essential surjectivity.  They make no
fullness, faithfulness, equivalence, or K-theory claim.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationFundamentalGroupoidTests

variable (X : SSet.{u})

example : SSet.FundamentalGroupoid X ⥤
    _root_.FundamentalGroupoid (SSet.toTop.obj X) :=
  SSet.realizationFundamentalGroupoidFunctor X

example (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidFunctor X).obj
        (SSet.FundamentalGroupoid.mk x) =
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex x) :=
  SSet.realizationFundamentalGroupoidFunctor_obj_mk X x

example {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.realizationFundamentalGroupoidFunctor X).map
        (SSet.FundamentalGroupoid.homMk e) =
      Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath e)) :=
  SSet.realizationFundamentalGroupoidFunctor_map_homMk X e

/-- The realized representative relation retains the simplicial convention
`e₀₁ ; e₁₂ = e₀₂`. -/
example {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (SSet.realizationFundamentalGroupoidFunctor X).map
          (SSet.FundamentalGroupoid.homMk e₀₁) ≫
        (SSet.realizationFundamentalGroupoidFunctor X).map
          (SSet.FundamentalGroupoid.homMk e₁₂) =
      (SSet.realizationFundamentalGroupoidFunctor X).map
        (SSet.FundamentalGroupoid.homMk e₀₂) := by
  simpa only [Functor.map_comp]
    using (SSet.realizationFundamentalGroupoidFunctor X).congr_map
      h.homMk_comp

example : (SSet.realizationFundamentalGroupoidFunctor X).EssSurj :=
  SSet.realizationFundamentalGroupoidFunctor_essSurj X

example (y : _root_.FundamentalGroupoid (SSet.toTop.obj X)) :
    (SSet.realizationFundamentalGroupoidFunctor X).essImage y :=
  (SSet.realizationFundamentalGroupoidFunctor_essSurj X).mem_essImage y

end RealizationFundamentalGroupoidTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
