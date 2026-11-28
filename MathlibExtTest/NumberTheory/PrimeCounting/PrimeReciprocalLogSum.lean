/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.PrimeReciprocalLogSum

/-!
# Tests for `∑_{p ≤ x/2} 1 / (p log(x/p))`
-/

@[expose] public section

open Finset Nat

example : ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
    ∑ p ∈ primesLE ⌊x / 2⌋₊, (1 : ℝ) / (p * Real.log (x / p)) ≤
      C * Real.log (Real.log x) / Real.log x :=
  sum_primesLE_inv_mul_log_div_le

-- At the left endpoint `x = 3` the sum is empty, since `⌊3 / 2⌋ = 1` and `primesLE 1 = ∅`.
example : primesLE ⌊(3 : ℝ) / 2⌋₊ = ∅ := by
  rw [show ⌊(3 : ℝ) / 2⌋₊ = 1 by norm_num [Nat.floor_eq_iff]]
  decide
