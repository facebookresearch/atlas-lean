/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CountBootstrap

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CountBootstrap`

In the plane:
* `bc85_finiteN_not_enough_note` at `L = 3` (upper lines: a `Gn` trifurcation with disjoint buffer
  boxes and connected arms);
* `bc85_status`: the upper lines have `N = ⊤`, and `N < ⊤` a.s. iff `N = ⊤` is null, for
  Bernoulli(1/2);
* `bc85_exclude_infinite_N` applied to Bernoulli(1/2).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CountBootstrap

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The Bernoulli(1/2) bond percolation measure on the planar lattice. -/
noncomputable abbrev bern2 : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)

/-- `bern2` has finite energy. -/
theorem bern2_fe : HasFiniteEnergyMerge bern2 :=
  bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)

/-- `bern2` is translation invariant. -/
theorem bern2_inv : IsTranslationInvariant (G := Multiplicative (Site 2)) bern2 :=
  (bkc_bernoulli_isErgodic (d := 2) (by norm_num) _ _).isTranslationInvariant

-- The upper-lines example at `L = 3`.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 3 (0 : Site 2)) (bc61_boxAround 2 3 (bc76_yBuf 3)) :=
  ⟨(bc85_finiteN_not_enough_note le_rfl).1, (bc85_finiteN_not_enough_note le_rfl).2.1⟩

-- The upper lines have infinitely many infinite clusters.
example : numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc85_status.2.2.2.2

-- For Bernoulli(1/2): `N < ⊤` almost surely iff `N = ⊤` is null.
example : bern2 {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔
    bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc85_status.2.2.1 bern2

-- No coarse trifurcations plus the coarse step exclude `N = ⊤`.
example (L : ℕ) (h0 : bern2 {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence bern2 L) : bern2 {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc85_exclude_infinite_N bern2 L h0 hexist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CountBootstrap
