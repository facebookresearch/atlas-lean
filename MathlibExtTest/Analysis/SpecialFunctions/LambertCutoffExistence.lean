/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.LambertWFunction

/-! # Tests for the endpoint of the Lambert cutoff existence theorem -/

open MetaMathlibExt Real

-- A client needs only the Lambert API to use the boundary case `n = 4`, `c = 1`.
example : ∃ a : ℝ, 3 ≤ a ∧ lambertMap (-a / 3) = -(1 / 3) := by
  have h := exists_lambertSequence (n := 4) (c := 1) (by decide) zero_lt_one le_rfl
  simpa only [show ((4 : ℕ) : ℝ) - 1 = 3 by norm_num, one_rpow, mul_one] using h

-- Independently certify the boundary case from the lower preimage of `-1/3`.
example : ∃ a : ℝ, 3 ≤ a ∧ lambertMap (-a / 3) = -(1 / 3) := by
  have he : exp 1 < 3 := by
    have h := (abs_le.mp (exp_bound (x := 1) (by norm_num) (n := 3) (by decide))).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hlower : (1 / 3 : ℝ) < exp (-1) := by
    rw [exp_neg, lt_inv_comm₀ (by norm_num) (exp_pos 1)]
    simpa using he
  obtain ⟨⟨y, hy⟩, hW⟩ := (existsUnique_lambertMap_lower_preimage (x := -(1 / 3 : ℝ))
    (by linarith) (by norm_num)).exists
  refine ⟨-3 * y, by linarith, ?_⟩
  rwa [show -(-3 * y) / 3 = y by ring]
