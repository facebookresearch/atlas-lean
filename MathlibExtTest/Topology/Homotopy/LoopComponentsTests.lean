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

import MathlibExt.Topology.Homotopy.LoopComponents

/-!
# Loop-component tests

These tests pin the generic equivalence from loop-space components to the
fundamental group and its action on loop representatives.  They make no
realization, model-category, or K-theory claim.
-/

universe u

namespace MathlibExtTest.Topology.Homotopy.LoopComponentsTests

variable {X : Type u} [TopologicalSpace X] (x : X)

noncomputable example :
    ZerothHomotopy (LoopSpace X x) ≃ FundamentalGroup X x :=
  loopComponentsEquivFundamentalGroup X x

example (p : LoopSpace X x) :
    loopComponentsEquivFundamentalGroup X x (ZerothHomotopy.mk p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :=
  loopComponentsEquivFundamentalGroup_mk p

end MathlibExtTest.Topology.Homotopy.LoopComponentsTests
