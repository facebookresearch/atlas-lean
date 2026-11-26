/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndexBinomidUpperAverageEqISup

/-! # Tests for `MathlibExt.NumberTheory.BinomidIndexBinomidUpperAverageEqISup` -/

namespace MathlibExtTest.NumberTheory.BinomidIndexBinomidUpperAverageEqISup

open MetaMathlibExt

/-- For a constant sequence the supremum of the averages is the constant. -/
example (c : ℕ) :
    (⨆ i : ℕ, ⨆ (_ : 1 ≤ i), ((binomidAverage (fun _ => c) i : ℝ) : EReal))
      = ((c : ℝ) : EReal) := by
  rw [← (isBinomidIndex_const c).binomidUpperAverage_eq_iSup, binomidUpperAverage_const]

/-- Every initial average of a binomid index is bounded by its upper average. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) {i : ℕ} (hi : 1 ≤ i) :
    ((binomidAverage η i : ℝ) : EReal) ≤ binomidUpperAverage η := by
  rw [hη.binomidUpperAverage_eq_iSup]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

/-- The identity sequence has average `1 / 2` at length two, bounding its upper average. -/
example : (((1 / 2 : ℚ) : ℝ) : EReal) ≤ binomidUpperAverage (fun i => i) := by
  have hη : IsBinomidIndex (fun i => i) := isBinomidIndex_of_monotone fun _ _ hij => hij
  have h2 : binomidAverage (fun i => i) 2 = 1 / 2 := by
    simp [binomidAverage, Finset.sum_range_succ]
  rw [← h2, hη.binomidUpperAverage_eq_iSup]
  exact le_iSup_of_le 2 (le_iSup_of_le (by decide) le_rfl)

end MathlibExtTest.NumberTheory.BinomidIndexBinomidUpperAverageEqISup
