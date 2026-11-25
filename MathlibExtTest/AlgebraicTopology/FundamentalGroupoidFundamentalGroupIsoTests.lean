/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso

/-! # Tests for fundamental groups under topological isomorphisms -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace FundamentalGroupIsoTests

variable {X Y : TopCat.{u}} (e : X ≅ Y)
  (x : X) (y : Y) (hxy : e.hom x = y)

example : FundamentalGroup X x ≃* FundamentalGroup Y y :=
  FundamentalGroup.mulEquivOfIsoAt e x y hxy

example (q : FundamentalGroup X x) :
    FundamentalGroup.mulEquivOfIsoAt e x y hxy q =
      FundamentalGroup.mapOfEq e.hom.hom hxy q :=
  FundamentalGroup.mulEquivOfIsoAt_apply e x y hxy q

end FundamentalGroupIsoTests

end
