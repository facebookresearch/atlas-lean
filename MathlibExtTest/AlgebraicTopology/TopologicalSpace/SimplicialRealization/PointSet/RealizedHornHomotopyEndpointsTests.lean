/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopyEndpoints

@[expose] public section

/-!
# Realized horn homotopy endpoints client test

Minimal downstream client for `SSet.realizedHornHomotopyMap_one` and
`SSet.realizedHornHomotopyMap_fix`.
Restates exact interval-one and fix equalities at universe-zero with no new reasoning.
No Homotopy package, weak equivalence, fibration, product, colimit, or model-category claim.
-/

set_option autoImplicit false

open scoped Simplicial unitInterval

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyEndpointsTests

theorem realizedHornHomotopyMap_one_client (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : ↥(SSet.toTop.obj (Δ[n] : SSet.{0}))) :
    SSet.realizedHornHomotopyMap n k hn (1, x) =
      SSet.toTop.map (SSet.horn n k).ι (SSet.realizedHornRetract n k hn x) :=
  SSet.realizedHornHomotopyMap_one n k hn x

theorem realizedHornHomotopyMap_fix_client (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (y : SSet.toTop.obj (SSet.horn n k)) (t : I) :
    SSet.realizedHornHomotopyMap n k hn (t, SSet.toTop.map (SSet.horn n k).ι y) =
      SSet.toTop.map (SSet.horn n k).ι y :=
  SSet.realizedHornHomotopyMap_fix n k hn y t

#print axioms SSet.realizedHornHomotopyMap_one
#print axioms SSet.realizedHornHomotopyMap_fix
#print axioms realizedHornHomotopyMap_one_client
#print axioms realizedHornHomotopyMap_fix_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornHomotopyEndpointsTests
