/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.HBCCalibrating
import Mathlib.Tactic.NormNum

/-! # Tests for the product identities for HBC calibrating numbers -/

open MetaMathlibExt Finset

-- A singleton uses the terminal factor even at index one.
example (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    1 - 1 / (((a : ℚ) + d) / d) = a / ((a : ℚ) + d) := by
  simpa using (hbcCalibrating_prod_identities a d 1 ha hd le_rfl).1

-- With a = 4 and d = 6, both α and d/a are nonintegral.
-- The first two terms are 8/3 and 34/9 whenever the terminal index is larger than two.
example (k : ℕ) (hk : 2 < k) :
    let α : ℚ := 5 / 3
    let n : ℕ → ℚ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    ∏ i ∈ Icc 1 2, n i = 272 / 27 := by
  have h := (hbcCalibrating_prod_identities 4 6 k (by decide) (by decide) (by omega)).2.1
    2 (by decide) hk
  norm_num at h ⊢
  exact h

-- At length two the second term is 25/9, giving a different product at the same endpoint.
example :
    let α : ℚ := 5 / 3
    let n : ℕ → ℚ := fun i => if i < 2 then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ 1
    ∏ i ∈ Icc 1 2, n i = 200 / 27 := by
  have h := (hbcCalibrating_prod_identities 4 6 2 (by decide) (by decide) (by decide)).2.2
  norm_num at h ⊢
  exact h
