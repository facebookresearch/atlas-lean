/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ThresholdLift

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ThresholdLift`

* `thresholdLift_of_logisticDiffineq` for `f = id` on `[1/2, 1]` with `κ = 1`: the logistic
  inequality `p (1 - p) ≤ 1 = f'` holds, giving `1 - exp (-1/4) ≤ 1`;
* `thresholdLift_logScale` for the same `f` with `n = 2`, `c = 1` (using `log 2 < 1`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ThresholdLift

open _root_.StatMech _root_.StatMech.BeffaraDC Set

-- `f = id` satisfies the logistic differential inequality on `[1/2, 1]` with `κ = 1`.
example : 1 - Real.exp (-1 * (1 / 2) * (1 - 1 / 2)) ≤ id (1 : ℝ) :=
  thresholdLift_of_logisticDiffineq id (fun _ => 1) (by norm_num) zero_le_one (by norm_num)
    (fun p hp => ⟨by simp only [id]; linarith [hp.1], hp.2⟩) (fun p _ => hasDerivAt_id p)
    (fun p hp => by simp only [id]; nlinarith [hp.1, hp.2]) (by simp)

-- The log-scale form at `n = 2`, `c = 1`.
example : 1 - ((2 : ℕ) : ℝ) ^ (-1 * (1 / 2) * (1 - 1 / 2) : ℝ) ≤ id (1 : ℝ) :=
  thresholdLift_logScale id (fun _ => 1) 2 (by norm_num) zero_le_one (by norm_num)
    (by norm_num) (fun p hp => ⟨by simp only [id]; linarith [hp.1], hp.2⟩)
    (fun p _ => hasDerivAt_id p)
    (fun p hp => by
      have h2 : Real.log ((2 : ℕ) : ℝ) < 1 := by
        have := Real.log_two_lt_d9
        push_cast
        linarith
      have h0 : 0 ≤ Real.log ((2 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
      simp only [id]
      nlinarith [hp.1, hp.2, mul_nonneg h0 (sub_nonneg.mpr hp.2)])
    (by simp)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ThresholdLift
