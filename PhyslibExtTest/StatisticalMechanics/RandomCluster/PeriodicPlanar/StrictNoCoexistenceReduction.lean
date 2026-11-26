/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.StrictNoCoexistenceReduction

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.StrictNoCoexistenceReduction`

A toy self-dual model at `q = 1` (`p* = 1 - p`), both predicates `p ↦ 1 / 2 < p`, `pc = pc* = 1/2`:
* `StrictDualNoCoexistence` holds for it (non-vacuity);
* `dualCritical_crossBounds_of_sharpness_strictNoCoexistence` gives the cross bound
  `1 / 2 ≤ (1/4)* = 3 / 4`;
* `dualCritical_relation_of_sharpness_strictNoCoexistence` gives `(1/2)* = 1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar
namespace StrictNoCoexistenceReduction

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

/-- The toy models satisfy strict no-coexistence. -/
theorem toy_strict :
    StrictDualNoCoexistence (fun p : ℝ => 1 / 2 < p) (fun p : ℝ => 1 / 2 < p) 1 := by
  rintro r _ p _ hrp ⟨h1, h2⟩
  simp only [dualParam_one] at h2
  linarith

-- A cross bound at `p = 1 / 4`.
example : (1 / 2 : ℝ) ≤ dualParam (1 / 4) 1 :=
  (dualCritical_crossBounds_of_sharpness_strictNoCoexistence one_pos toy_sharp toy_sharp
    toy_coverage toy_strict).1 (1 / 4) (by norm_num) (by norm_num)

-- The critical relation for the toy model.
example : dualParam (1 / 2) 1 = 1 / 2 :=
  (dualCritical_relation_of_sharpness_strictNoCoexistence (by norm_num) (by norm_num) one_pos
    toy_sharp toy_sharp toy_coverage toy_strict).1

end StrictNoCoexistenceReduction
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar
