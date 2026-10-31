/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Filter.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction

/-!
# Positive probability of three separated clusters at the origin

If `N = ∞` has positive Bernoulli probability, some triple of sites in a box lies in three distinct
infinite clusters with positive probability.

## i. Overview

`bxp_Y` is the event that the sites `b_i` of `MergeFree` lie in infinite, pairwise disconnected
clusters avoiding the origin; it is contained in the precursor event `bmf_X`. `bxp_tripleEvent d n x
y z` is the event that `N = ∞` and the three box sites lie in distinct infinite clusters. The event
`threeMeetBox d n` is the countable union of these, so positive probability of `N = ∞` gives a
triple with positive probability.

## ii. Key results

- `bxp_Y_subset_X` : `bxp_Y` lies in the precursor event
- `bxp_threeMeetBox_subset_iUnion` : `threeMeetBox` is a union of triple events
- `bxp_exists_triple_pos` : some triple event has positive probability

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

variable {d : ℕ}

/-! ## A. Results -/

lemma bxp_notConnected_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d}
    (h : ¬ Connected d ω a b) : ¬ Connected d (removeSite 0 ω) a b :=
  fun hc => h (ava_connected_of_removeSite ω hc)

/-- The sites `b_i` lie in infinite, pairwise disconnected clusters avoiding the origin. -/
def bxp_Y : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω |
    ((0 : Site 2) ∉ cluster 2 ω bmf_b₁ ∧ (0 : Site 2) ∉ cluster 2 ω bmf_b₂ ∧
      (0 : Site 2) ∉ cluster 2 ω bmf_b₃) ∧
    ((cluster 2 ω bmf_b₁).Infinite ∧ (cluster 2 ω bmf_b₂).Infinite ∧
      (cluster 2 ω bmf_b₃).Infinite) ∧
    (¬ Connected 2 ω bmf_b₁ bmf_b₂ ∧ ¬ Connected 2 ω bmf_b₁ bmf_b₃ ∧
      ¬ Connected 2 ω bmf_b₂ bmf_b₃)}

lemma bxp_Y_subset_X : bxp_Y ⊆ bmf_X := by
  rintro ω ⟨⟨h01, h02, h03⟩, ⟨hi1, hi2, hi3⟩, ⟨hd12, hd13, hd23⟩⟩
  exact ⟨⟨bc20_removeSite_infinite_of_originFree ω _ h01 hi1, bc20_removeSite_infinite_of_originFree ω _ h02 hi2,
      bc20_removeSite_infinite_of_originFree ω _ h03 hi3⟩,
    bxp_notConnected_removeSite ω hd12, bxp_notConnected_removeSite ω hd13,
    bxp_notConnected_removeSite ω hd23⟩

lemma bxp_hXpos_of_fullPos (p : ℝ≥0) (hp1 : p ≤ 1)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bxp_Y) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X :=
  lt_of_lt_of_le hpos (measure_mono bxp_Y_subset_X)

/-- `N = ∞` and the box sites `x, y, z` lie in three pairwise distinct infinite clusters. -/
def bxp_tripleEvent (d n : ℕ) (x y z : Site d) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = ⊤ ∧ x ∈ box d n ∧ y ∈ box d n ∧ z ∈ box d n ∧
    (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧ (cluster d ω z).Infinite ∧
    cluster d ω x ≠ cluster d ω y ∧ cluster d ω x ≠ cluster d ω z ∧
    cluster d ω y ≠ cluster d ω z}

lemma bxp_threeMeetBox_subset_iUnion (d n : ℕ) :
    threeMeetBox d n ⊆ ⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z := by
  intro ω hω
  obtain ⟨htop, x, y, z, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩ := hω
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨z,
    htop, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩⟩⟩

lemma bxp_exists_triple_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ (n : ℕ) (x y z : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bxp_tripleEvent d n x y z) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z) = 0 := by
    refine measure_iUnion_null fun x => measure_iUnion_null fun y =>
      measure_iUnion_null fun z => ?_
    exact hcon n x y z
  have h0 : μ (threeMeetBox d n) = 0 :=
    le_antisymm ((measure_mono (bxp_threeMeetBox_subset_iUnion d n)).trans_eq hu) bot_le
  exact absurd h0 (ne_of_gt hn)

end StatMech.Walls
