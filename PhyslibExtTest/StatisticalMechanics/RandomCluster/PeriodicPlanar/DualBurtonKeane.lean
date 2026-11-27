/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualBurtonKeane

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualBurtonKeane`

* the all-closed configuration of the square lattice has no infinite cluster, and by
  `hasInfiniteCluster_configTranslate` neither has its translate by `(1, 0)`;
* `hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one` in its conditional form on the
  square lattice;
* `freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one` instantiated for an
  arbitrary dual pair at `p = 1 / 2`, `q = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualBurtonKeane

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice MeasureTheory

/-- The all-closed configuration of the square lattice has no infinite cluster. -/
theorem allClosed_not_hasInfiniteCluster :
    ¬ square.HasInfiniteCluster (fun _ => false) := by
  rintro ⟨x, hx⟩
  apply hx
  apply (Set.finite_singleton x).subset
  intro w hw
  obtain ⟨p⟩ := (hw : (square.openSubgraph fun _ => false).Reachable x w)
  cases p with
  | nil => rfl
  | cons h _ =>
    rw [PeriodicGraph.openSubgraph_adj] at h
    exact absurd h.2 Bool.false_ne_true

-- Translation invariance of the infinite-cluster event, at the all-closed configuration.
example : ¬ square.HasInfiniteCluster (square.configTranslate ![1, 0] fun _ => false) := by
  rw [PeriodicGraph.hasInfiniteCluster_configTranslate]
  exact allClosed_not_hasInfiniteCluster

-- Zero-one law plus almost sure existence gives almost sure uniqueness (conditional form).
example (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (h1 : mu {omega | square.numInfiniteClusters omega = 1} = 1)
    (hinf : mu {omega | square.HasInfiniteCluster omega} = 1) :
    mu {omega | square.HasUniqueInfiniteCluster omega} = 1 :=
  square.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one mu ⟨1, h1, Or.inr rfl⟩ hinf

-- Common primal and dual uniqueness for an arbitrary dual pair (conditional form).
example {V W : Type} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W} (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    (hprimal : 0 < (P.freeBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure _).real P.percolationEvent)
    (hdual : 0 < (D.dualMeasure (P.freeBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num) (zero_lt_one.trans_le le_rfl) : Measure _)).real Pdual.percolationEvent) :
    (P.freeBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure _) D.commonUniqueInfiniteClusterEvent = 1 :=
  D.freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one hconn hconnDual
    _ _ le_rfl hprimal hdual

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualBurtonKeane
