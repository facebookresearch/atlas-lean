/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount`

In the plane:
* `bc54_classicalTcount_le_boundary_succ_all` for the all-closed configuration at `n = 3`;
* `bc54_boundary_succ_vol_tendsto` at `d = 2`;
* `bc54_classicalTrif_prob_eq_zero` for Bernoulli(1/2) bond percolation;
* the witness `bc54_witness_boundary_trif_arm_inbox_succ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal
open Filter Topology

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The Bernoulli(1/2) bond percolation measure on the planar lattice. -/
noncomputable abbrev bern2 : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)

/-- `bern2` has finite energy. -/
theorem bern2_fe : HasFiniteEnergyMerge bern2 :=
  bkc_bernoulli_hasFiniteEnergyMerge _ _ (by norm_num)

/-- `bern2` is translation invariant. -/
theorem bern2_inv : IsTranslationInvariant (G := Multiplicative (Site 2)) bern2 :=
  (bkc_bernoulli_isErgodic (d := 2) (by norm_num) _ _).isTranslationInvariant

-- The classical count of the all-closed configuration is bounded by the next boundary.
example : bc48_Tcount_classical 2 closed2 3 ≤ boxSV_boundaryCard 2 (3 + 1) :=
  bc54_classicalTcount_le_boundary_succ_all closed2 (by norm_num) 3

-- The boundary-to-volume ratio vanishes in the plane.
example : Tendsto (fun n => (boxSV_boundaryCard 2 (n + 1) : ℝ) / ((boxFinsetBK 2 n).card : ℝ))
    atTop (𝓝 0) :=
  bc54_boundary_succ_vol_tendsto 2 (by norm_num)

-- Classical trifurcations at the origin have probability zero under Bernoulli(1/2).
example : bern2 {ω | bc47_IsClassicalTrifurcation ω 0} = 0 :=
  bc54_classicalTrif_prob_eq_zero bern2 (by norm_num) bern2_inv

-- The explicit witness site lies in the radius-2 box.
example : (![(2 : ℤ), 0] : Site 2) ∈ box 2 (1 + 1) :=
  bc54_witness_boundary_trif_arm_inbox_succ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount
