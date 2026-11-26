/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryBandAssembly

/-!
# Tests for `Sheffield.BoundaryBandAssembly`

Module under test: `Sheffield.BoundaryBandAssembly` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* Refutation: `PeriodicPlanarDualPair.TwoLevelRectangleArray` is empty for every dual pair,
  probability measure and arc bound (`TwoLevelRectangleArray.false`, stated as `IsEmpty`).
* `PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed`,
  `PeriodicPlaneEmbedding.NormalBoundaryBandSeed.toCommonSquare` and
  `PeriodicPlaneEmbedding.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one`
  elaborate (check-only; no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace BoundaryBandAssembly

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Two-level primal/dual rectangle arrays do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (B : ℝ) : IsEmpty (D.TwoLevelRectangleArray mu B) :=
  ⟨PeriodicPlanarDualPair.TwoLevelRectangleArray.false D mu⟩

-- `PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed` elaborates.
example := @PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed

-- `PeriodicPlaneEmbedding.NormalBoundaryBandSeed.toCommonSquare` elaborates.
example := @PeriodicPlaneEmbedding.NormalBoundaryBandSeed.toCommonSquare

open PeriodicPlaneEmbedding in
example := @exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one

end BoundaryBandAssembly
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
