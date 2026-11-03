/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusBoundaryReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusBoundaryReach`

On the `3 × 3` torus:
* `triangularTorusActiveReachIndicator` is `0` for the empty target and `1` when the target
  contains the start site;
* `triangularTorusActiveReachIndicator_eq_eventIndicator` (indicator of the reach event);
* `triHexFK_torus_homogeneous_activeReachProbability_eq` at `q = 4`, `p = 1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusBoundaryReach

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex _root_.StatMech.FK
open _root_.StatMech.BeffaraDC

/-- The `3 × 3` torus is admissible. -/
local instance fact_two_lt_three : Fact (2 < 3) := ⟨by norm_num⟩

-- Nothing reaches the empty target; the start site reaches any target containing it.
example (x : TorusSite 3) (omega : _root_.StatMech.ConfigSpace (triangularTorusGraph 3).edgeSet) :
    triangularTorusActiveReachIndicator 3 x ∅ omega = 0 ∧
      triangularTorusActiveReachIndicator 3 x {x} omega = 1 := by
  constructor <;> simp [triangularTorusActiveReachIndicator]

-- The indicator is that of the reach event.
example (x : TorusSite 3) (target : Finset (TorusSite 3)) :
    triangularTorusActiveReachIndicator 3 x target =
      (triangularTorusActiveReachEvent 3 x target).indicator (fun _ => (1 : ℝ)) :=
  triangularTorusActiveReachIndicator_eq_eventIndicator 3 x target

-- Reach probabilities agree at the critical point `p = 1/2`, `q = 4`.
example (x : TorusSite 3) (target : Finset (TorusSite 3)) :
    activeProbOf (hexagonalTorusGraph 3) (fun _ => dualParam (1 / 2) 4) 4
        (hexagonalTorusActiveWhiteReachEvent 3 x target) =
      activeProbOf (triangularTorusGraph 3) (fun _ => 1 / 2) 4
        (triangularTorusActiveReachEvent 3 x target) :=
  triHexFK_torus_homogeneous_activeReachProbability_eq 3 (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num [triangularFKCriticalPolynomial, fkEdgeOdds]) x target

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusBoundaryReach
