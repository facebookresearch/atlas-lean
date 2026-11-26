/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorRouting`

* `brt2_posRouting_of_routingCover`, `brt2_route_of_posRouting` and
  `brt2_bk_atLeastTwo_of_posRouting` in conditional form (positive routing at every scale gives
  precursors and excludes two infinite clusters);
* `brt2_precursor_pos_of_forceOpen_pos` with the empty edge set: positivity transfers to the
  precursor itself.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorRouting

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory _root_.StatMech.ConfigSpace
open scoped NNReal

variable {d : ℕ}

-- A routing cover gives positive routing.
example (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ) (hrt : hrHD_DisjointRouting d n) :
    brt2_PosRouting (d := d) p hp1 n :=
  brt2_posRouting_of_routingCover p hp1 hrt

-- Positive routing turns three clusters meeting a box into a positive-probability precursor.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n)
    (n : ℕ) (h3 : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ : Site d,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  brt2_route_of_posRouting p hp1 hp0 hpr n h3

-- Positive routing at every scale excludes two infinite clusters.
example (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  brt2_bk_atLeastTwo_of_posRouting hd p hp1 hp0 hpr

-- With no forced edges, positivity of the forced event is positivity of the precursor.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ ((fun ω => forceOpenFinset ∅ ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  brt2_precursor_pos_of_forceOpen_pos μ hfe ∅ a₁ a₂ a₃ hpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorRouting
