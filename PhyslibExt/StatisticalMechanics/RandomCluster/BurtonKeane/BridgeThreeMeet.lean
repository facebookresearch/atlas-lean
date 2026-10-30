/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CylinderResidue

/-!
# The bridge to triple events

Three infinite clusters meeting a box force infinitely many infinite clusters and a
positive-probability triple event; the bridge from triple events to cylinder patterns gives the
route and uniqueness.

## i. Overview

`threeMeetBox 2 n` is contained in the event `N = ⊤`, and if it has positive probability then so
does a triple event `bxp_tripleEvent`. The bridge `bcl2_Bridge p hp1` asks every
positive-probability triple event for a cylinder pattern and external event producing a neighbour
precursor. It gives the route and uniqueness on `ℤ²` for `0 < p < 1`.

The uniqueness theorems here assume the bridge, which is not proved in this module.

## ii. Key results

- `bcl2_tripleEvent_pos_of_threeMeetBox` : a positive triple event from three clusters meeting a
  box.
- `bcl2_bk_of_bridge` : uniqueness from the bridge.

## iii. Table of contents

- A. Triple events
- B. The bridge

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option maxRecDepth 4000

/-! ## A. Triple events -/

lemma bcl2_threeMeetBox_subset_top (n : ℕ) :
    threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} := by
  intro ω hω
  exact hω.1

lemma bcl2_tripleEvent_pos_of_threeMeetBox (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ (m : ℕ) (x y z : Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) := by
  have htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
    lt_of_lt_of_le hpos (measure_mono (bcl2_threeMeetBox_subset_top n))
  exact bxp_exists_triple_pos (d := 2) p hp1 htop

/-! ## B. The bridge -/

/-- Bridge: every positive-probability triple event has a finite cylinder pattern and an extension
event
of positive probability that together produce a neighbour trifurcation precursor. -/
def bcl2_Bridge (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  ∀ (m : ℕ) (x y z : Site 2),
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) →
      ∃ (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2) (η₀ : ConfigSpace ↥I),
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
          (hypercubicLattice 2).Adj 0 a₃) ∧
        (∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
          Connected 2 (removeSite 0 ω) a₁ x ∧ Connected 2 (removeSite 0 ω) a₂ y ∧
            Connected 2 (removeSite 0 ω) a₃ z) ∧
        MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x y z) ∧
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (bpt2_Ext I a₁ a₂ a₃ x y z)

lemma bcl2_hroute_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n hpos
  obtain ⟨m, x, y, z, htriple⟩ := bcl2_tripleEvent_pos_of_threeMeetBox p hp1 n hpos
  obtain ⟨I, a₁, a₂, a₃, η₀, hne, hadj, hcorr, hExtMeas, hXpos⟩ := hbridge m x y z htriple
  exact ⟨a₁, a₂, a₃,
    bcl_precursorPos p hp1 hp0 hplt I a₁ a₂ a₃ x y z η₀ hne hadj hcorr hExtMeas hXpos⟩

lemma bcl2_bk_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bcl2_hroute_of_bridge p hp1 hp0 hplt hbridge)

lemma bcl2_bk_atLeastTwo_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bcl2_bk_of_bridge p hp1 hp0 hplt hbridge).2.1

end StatMech.Walls
