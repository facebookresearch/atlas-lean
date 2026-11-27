/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopyEndpoints

/-!
# Homotopy from a realized simplex to a horn retract

For a positive dimension `n` and horn index `k : Fin (n + 1)`, the realized
simplex has a continuous horn retraction `r : |Δ[n]| → |Λ[n,k]|`.
The realized horn homotopy runs from the identity at time zero to the composite
of `r` with the horn inclusion at time one, in every simplicial-set universe.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

namespace SSet

/--
For `n > 0`, the continuous homotopy from the identity of `|Δ[n]|` to horn
retraction followed by the inclusion `|Λ[n,k]| → |Δ[n]|`.
-/
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
