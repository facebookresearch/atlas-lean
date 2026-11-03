/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnector

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnector`

* `PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent` is an event (a set of
  configurations) for explicit parameters `r = 0`, `R = 1`, `c = -1`, `d = 1`.
* `PeriodicPlaneEmbedding.deepOpenExitedJoinedBoundaryArmEvent_tendsto_one` specialized to a
  constant schedule (all parameters fixed in `n`): the arm and merge limits then become the
  hypotheses of the specialization.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnector

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- The deep connector event at explicit parameters.
example (E : PeriodicPlaneEmbedding P) (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  E.deepOpenExitedJoinedBoundaryArmEvent 0 1 (-1) 1 L U

-- The limit statement for a constant schedule.
example (E : PeriodicPlaneEmbedding P) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (r R c d : ℝ) (L U : Finset V) :=
  E.deepOpenExitedJoinedBoundaryArmEvent_tendsto_one mu (fun _ => r) (fun _ => R) (fun _ => c)
    (fun _ => d) (fun _ => L) (fun _ => U)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnector
