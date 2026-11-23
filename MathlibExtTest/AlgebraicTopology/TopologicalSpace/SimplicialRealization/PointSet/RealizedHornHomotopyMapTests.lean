/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopyMap

@[expose] public section

/-!
# Realized horn homotopy map zero-law client test

Minimal downstream client for `SSet.realizedHornHomotopyMap_zero`.
Restates exact interval-zero equality at universe-zero with no new reasoning.
No reproof or extra endpoint claim.
-/

set_option autoImplicit false

open scoped Simplicial unitInterval

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyMapTests

theorem realizedHornHomotopyMap_zero_client (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : ↥(SSet.toTop.obj (Δ[n] : SSet.{0}))) :
    SSet.realizedHornHomotopyMap n k hn (0, x) = x :=
  SSet.realizedHornHomotopyMap_zero n k hn x

#print axioms SSet.realizedHornHomotopyMap_zero
#print axioms realizedHornHomotopyMap_zero_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyMapTests
