/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorCage

/-!
# Tests for `Sheffield.DeepConnectorCage`

Module under test: `Sheffield.DeepConnectorCage` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent` at explicit parameters.
* `PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one` specialized to a
  constant schedule.
* `PeriodicPlanarDualPair.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent`
  and `…_disjoint_boundaryBand_of_subset_cage` elaborate (check-only; their geometric hypotheses
  need a concrete planar dual pair).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DeepConnectorCage

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- The finite deep connector event at explicit parameters (strip width `3`).
example (E : PeriodicPlaneEmbedding P) (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  E.finiteDeepOpenExitedJoinedBoundaryArmEvent 0 1 (-1) 1 3 L U

-- The limit statement for a constant schedule.
example (E : PeriodicPlaneEmbedding P) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (r R c d : ℝ) (w : ℕ) (L U : Finset V) :=
  E.finiteDeepOpenExitedJoinedBoundaryArmEvent_tendsto_one mu (fun _ => r) (fun _ => R)
    (fun _ => c) (fun _ => d) (fun _ => w) (fun _ => L) (fun _ => U)

open PeriodicPlanarDualPair in
example := @finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent

open PeriodicPlanarDualPair in
example := @finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage

end DeepConnectorCage
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
