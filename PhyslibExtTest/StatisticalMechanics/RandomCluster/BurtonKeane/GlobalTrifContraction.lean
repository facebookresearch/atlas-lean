/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalTrifContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalTrifContraction`

* `bgn_crossing_witness`: the explicit graph `bgn_W` has crossing boundary classes for the two
  centres `0` and `1` (instance).
* The first conjunct of `bgn_status` at `L = 1`: two upper-line sites share a contracted index.
* `bgn_sameTrif_classes_laminar` on the all-closed configuration (instance).
* The fourth conjunct: classical forest data are the global contracted forest.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalTrifContraction

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Two centres with crossing classes in `bgn_W`.
example : (bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4 :=
  bgn_crossing_witness.2.2.2.1

-- At `L = 1` the sites `(2, 1)` and `(3, 0)` share a contracted index, unlike the origin.
example : bgn_idx 1 (bc57_pt ((1 : ℕ) + 1) 1) = bgn_idx 1 (bc57_pt (2 * (1 : ℕ) + 1) 0) ∧
    bgn_idx 1 (bc57_pt ((1 : ℕ) + 1) 1) ≠ bgn_idx 1 (0 : Site 2) :=
  (bgn_status (d := 2)).1 1 le_rfl

-- Classes for the same centre are equal or disjoint.
example (u a b : Site 2) : bgn_boundaryClass (fun _ => false) 2 3 u a =
    bgn_boundaryClass (fun _ => false) 2 3 u b ∨
    Disjoint (bgn_boundaryClass (fun _ => false) 2 3 u a)
      (bgn_boundaryClass (fun _ => false) 2 3 u b) :=
  bgn_sameTrif_classes_laminar _ 2 3 u a b

-- Classical forest data are the global contracted forest.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) :
    bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R :=
  (bgn_status (d := 2)).2.2.2.1 ω L R

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalTrifContraction
