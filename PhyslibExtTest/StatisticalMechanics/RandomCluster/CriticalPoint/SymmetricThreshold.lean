/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SymmetricThreshold

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SymmetricThreshold`

* `symmetricThreshold_of_maxInfluence` at `n = edgeCount = 2`, `μ = 1/2`, `c_R = c_M = 1`, with
  derivative, total and maximal influence all equal to `log 2 / 8`: the three hypotheses hold
  (with equality), so the conditional statement is non-vacuous and gives `log 2 / 8 ≤ log 2 / 8`;
* the conclusion is positive there (`0 < log 2 / 8`), so the bound is not trivially `0 ≤ deriv`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.SymmetricThreshold

open _root_.StatMech _root_.StatMech.BeffaraDC

-- All three inputs hold at the explicit point.
example : (1 * 1 / 2) * (1 / 2 : ℝ) * (1 - 1 / 2) * Real.log ((2 : ℕ) : ℝ) ≤ Real.log 2 / 8 :=
  symmetricThreshold_of_maxInfluence (n := 2) (edgeCount := 2) (totalInfluence := Real.log 2 / 8)
    (maxInfluence := Real.log 2 / 8) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (le_of_eq (one_mul _))
    (le_of_eq (by push_cast; ring)) (le_of_eq (by push_cast; ring))

-- The lower bound at that point is strictly positive.
example : 0 < (1 * 1 / 2) * (1 / 2 : ℝ) * (1 - 1 / 2) * Real.log ((2 : ℕ) : ℝ) := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  push_cast
  positivity

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.SymmetricThreshold
