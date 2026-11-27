/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Rotated

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Rotated`

* `PeriodicPlanarDualPair.matchedVerticalHorizontalCrossingEvents_disjoint` and
  `matchedVerticalHorizontalCrossing_measureReal_add_le_one` for an arbitrary dual pair with arc
  bound `1` on the explicit rectangle `[0, 20]²`.
* `PeriodicPlanarDualPair.exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max` for constant
  rectangle sequences `[0, 1]²`.
* `PeriodicPlanarDualPair.balanced_aspect_contradiction_of_crossing_limits` elaborates
  (check-only; its conclusion is `False` and its hypotheses are jointly unsatisfiable by
  design).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Rotated

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Matched primal vertical and dual horizontal crossings of `[0, 20]²` are disjoint.
example (D : PeriodicPlanarDualPair P Pdual)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ 1)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ 1) :=
  PeriodicPlanarDualPair.matchedVerticalHorizontalCrossingEvents_disjoint D (a := 0) (b := 20)
    (c := 0) (d := 20) one_pos hBp hBd (by norm_num) (by norm_num)

-- Their probabilities sum to at most one.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ 1)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ 1) :=
  PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one D mu
    (a := 0) (b := 20) (c := 0) (d := 20) one_pos hBp hBd (by norm_num) (by norm_num)

-- A buffer for constant rectangle sequences.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] :=
  PeriodicPlanarDualPair.exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max D mu
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)

-- `PeriodicPlanarDualPair.balanced_aspect_contradiction_of_crossing_limits` elaborates.
example := @PeriodicPlanarDualPair.balanced_aspect_contradiction_of_crossing_limits

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Rotated
