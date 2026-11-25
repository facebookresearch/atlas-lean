/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopyEndpoints

/-!
# Realized horn homotopy package

For `0 < n` and `k : Fin (n + 1)`, the jointly continuous
`SSet.realizedHornHomotopyMap` packaged as a `ContinuousMap.Homotopy` from the
identity of the realized simplex to the realized horn inclusion after
`SSet.realizedHornRetract`. The endpoint laws are exactly
`realizedHornHomotopyMap_zero` at `0` and `realizedHornHomotopyMap_one` at `1`.

No filling, anodyne, weak-equivalence, fibration, product, colimit, or
model-category claim.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

namespace SSet

/-- Homotopy from the identity to inclusion after retraction. -/
noncomputable def realizedHornHomotopy (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (((SSet.toTop.map (SSet.horn.{u} n k).ι).hom).comp
        (SSet.realizedHornRetract n k hn)) where
  toContinuousMap := SSet.realizedHornHomotopyMap n k hn
  map_zero_left x := by
    simpa using SSet.realizedHornHomotopyMap_zero n k hn x
  map_one_left x := by
    simpa using SSet.realizedHornHomotopyMap_one n k hn x

end SSet
