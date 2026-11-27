/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction`

A toy self-dual model at `q = 1`, where `p* = 1 - p`: both predicates are `p ↦ 1 / 2 < p` and
`pc = pc* = 1 / 2`.
* `OffCriticalSharpness (1 / 2 < ·) (1 / 2)` holds (non-vacuity);
* `DualSubcriticalCoverage` and `DualNoCoexistence` hold for the toy model;
* `dualCritical_relation_of_sharpness_noCoexistence` then gives `(1/2)* = 1/2` and the odds
  product `1`;
* the square lattice does not wire-percolate at the out-of-range parameter `p = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.BeffaraDC

/-- At `q = 1` the dual parameter is `1 - p`. -/
theorem dualParam_one (p : ℝ) : dualParam p 1 = 1 - p := by
  have h : (1 - p) * 1 + p = 1 := by ring
  rw [dualParam, h, div_one, mul_one]

/-- The toy predicate is sharp at `1 / 2`. -/
theorem toy_sharp : OffCriticalSharpness (fun p : ℝ => 1 / 2 < p) (1 / 2) :=
  ⟨fun _ _ h => not_lt.2 h.le, fun _ _ h => h⟩

/-- The toy dual model percolates at `p*` below `1 / 2`. -/
theorem toy_coverage : DualSubcriticalCoverage (fun p : ℝ => 1 / 2 < p) (1 / 2) 1 := by
  intro p _ hp
  simp only [dualParam_one]
  linarith

/-- The toy models never percolate together. -/
theorem toy_noCoexistence :
    DualNoCoexistence (fun p : ℝ => 1 / 2 < p) (fun p : ℝ => 1 / 2 < p) 1 := by
  rintro p _ ⟨h1, h2⟩
  simp only [dualParam_one] at h2
  linarith

-- The abstract critical relation on the toy model.
example : dualParam (1 / 2) 1 = 1 / 2 ∧ (1 / 2 / (1 - 1 / 2)) * (1 / 2 / (1 - 1 / 2)) = (1 : ℝ) :=
  dualCritical_relation_of_sharpness_noCoexistence (by norm_num) (by norm_num) one_pos
    toy_sharp toy_sharp toy_coverage toy_noCoexistence

-- No wired percolation outside `(0, 1)`.
example : ¬ square.wiredPercolates 2 1 := by
  have h : square.wiredPercolationProbability 2 1 = 0 := by
    unfold PeriodicGraph.wiredPercolationProbability
    split_ifs with h2
    · exact absurd h2.1.2 (by norm_num)
    · rfl
  simp only [PeriodicGraph.wiredPercolates, h, lt_irrefl, not_false_eq_true]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction
