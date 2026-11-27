/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PatternSurgery

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PatternSurgery`

* `PeriodicPlanarDualPair.exists_primal_dual_open_iff_disjoint` for empty edge sets: a
  configuration opening both (empty) patterns exists, from the disjointness side of the iff.
* The same iff for a primal set `{e}` and an empty dual set.
* `PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_preserves_walks` and
  `measureReal_pos_of_primalDualOpenPattern_preimage` elaborate (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PatternSurgery

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Empty patterns are jointly openable.
example (D : PeriodicPlanarDualPair P Pdual) : ∃ omega : ConfigSpace (Sym2 V),
    (∀ e ∈ (∅ : Finset (Sym2 V)), omega e = true) ∧
      (∀ e ∈ (∅ : Finset (Sym2 W)), dualConfigEquiv D.edgeDual omega e = true) :=
  (D.exists_primal_dual_open_iff_disjoint ∅ ∅).mpr (Finset.disjoint_empty_left _)

-- A single primal edge with no dual constraint is openable.
example (D : PeriodicPlanarDualPair P Pdual) (e : Sym2 V) : ∃ omega : ConfigSpace (Sym2 V),
    (∀ e' ∈ ({e} : Finset (Sym2 V)), omega e' = true) ∧
      (∀ f ∈ (∅ : Finset (Sym2 W)), dualConfigEquiv D.edgeDual omega f = true) :=
  (D.exists_primal_dual_open_iff_disjoint {e} ∅).mpr (by simp)

-- `setPattern_primalDualOpenPattern_preserves_walks` elaborates.
example := @PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_preserves_walks

-- `measureReal_pos_of_primalDualOpenPattern_preimage` elaborates.
example := @PeriodicPlanarDualPair.measureReal_pos_of_primalDualOpenPattern_preimage

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PatternSurgery
