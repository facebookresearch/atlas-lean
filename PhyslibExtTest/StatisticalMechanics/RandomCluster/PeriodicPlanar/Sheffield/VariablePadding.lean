/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.VariablePadding

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.VariablePadding`

* `PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_pads` applied for an arbitrary
  dual pair with arc bound `B = 1`, pads `4` and the explicit rectangle `[0, 20] × [0, 20]`.
* Refutation: `VariablePadTwoLevelRectangleArray` is empty for every dual pair and probability
  measure (`VariablePadTwoLevelRectangleArray.elim`, stated as `IsEmpty`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.VariablePadding

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- The padded matched-crossing bound on `[0, 20]²` with arc bound `1` and pads `4`.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ 1)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ 1) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent 0 20 (0 + 4) (20 - 4)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent (0 + 4) (20 - 4) 0 20) ≤ 1 :=
  D.matchedCrossing_measureReal_add_le_one_of_pads mu one_pos hBp hBd (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- Variable-pad two-level rectangle arrays do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (B : ℝ) : IsEmpty (D.VariablePadTwoLevelRectangleArray mu B) :=
  ⟨PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.elim D mu⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.VariablePadding
