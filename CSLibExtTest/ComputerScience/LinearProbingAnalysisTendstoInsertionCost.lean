/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.ComputerScience.LinearProbingAnalysisTendstoInsertionCost
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tests for the fixed-load-factor limit of the insertion cost

Concrete instances of `tendsto_insertionCost`: empty tables and tables holding five items both
have mean insertion cost tending to `1`, the value `(1 + 1 / (1 - 0) ^ 2) / 2`.
-/

open Filter Topology

namespace CSLibExtTest.ComputerScience.LinearProbingAnalysisTendstoInsertionCost

open Cslib.Algorithms.Lean.LinearProbing

/-- Empty tables: the mean insertion cost tends to `(1 + 1 / (1 - 0) ^ 2) / 2 = 1`. -/
example : Tendsto (fun N : ℕ => (insertionCost N 0 : ℝ)) atTop (𝓝 1) := by
  have hlim : (1 + 1 / (1 - (0 : ℝ)) ^ 2) / 2 = 1 := by norm_num
  have h := tendsto_insertionCost 0 le_rfl (by norm_num) (fun _ => 0) (eventually_gt_atTop 0)
    (by simp)
  simpa [hlim] using h

/-- Tables holding five items: the mean insertion cost tends to `1`. -/
example : Tendsto (fun N : ℕ => (insertionCost N 5 : ℝ)) atTop (𝓝 1) := by
  have hlim : (1 + 1 / (1 - (0 : ℝ)) ^ 2) / 2 = 1 := by norm_num
  have h := tendsto_insertionCost 0 le_rfl (by norm_num) (fun _ => 5) (eventually_gt_atTop 5)
    (tendsto_const_div_atTop_nhds_zero_nat 5)
  simpa [hlim] using h

end CSLibExtTest.ComputerScience.LinearProbingAnalysisTendstoInsertionCost
