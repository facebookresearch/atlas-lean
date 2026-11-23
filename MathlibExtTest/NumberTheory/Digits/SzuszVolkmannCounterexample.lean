/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample

/-! # Integer values at the branch boundaries of Campbell's interpolation -/

open MetaMathlibExt

-- The last integer on the exponential branch still lies strictly between zero and one.
example : 0 < campbellF 9 ∧ campbellF 9 < 1 := by
  constructor
  · rw [campbellF, ite_eq_left (by norm_num : (9 : ℝ) ≤ 100 / 11)]
    positivity
  · have h := floor_campbellF_eq_campbellH2.1 9 (by decide)
    rw [campbellH2_small.1, Nat.cast_ofNat, Nat.floor_eq_zero] at h
    exact h

-- Ten is the right endpoint of the initial linear branch.
example : campbellF 10 = 10 := by
  simpa [campbellH2_small.2.1] using floor_campbellF_eq_campbellH2.2 10 le_rfl

-- At a change of decade the new block starts with its own initial value.
example : campbellF 99 = 900 ∧ campbellF 100 = 1000 := by
  constructor
  · simpa [campbellH2_small.2.2.2.1] using floor_campbellF_eq_campbellH2.2 99 (by decide)
  · simpa [campbellH2_small.2.2.2.2] using floor_campbellF_eq_campbellH2.2 100 (by decide)
