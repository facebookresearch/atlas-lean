/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.Choose.HockeyStickConvolution

/-! Tests for `MathlibExt.Data.Nat.Choose.HockeyStickConvolution`. -/

open Finset

-- `q = 0` specializes to the hockey-stick identity.
example (n p : ℕ) :
    ∑ ab ∈ antidiagonal n, ab.1.choose p * ab.2.choose 0 = (n + 1).choose (p + 1) := by
  simpa using Nat.sum_antidiagonal_choose_mul_choose n p 0

-- A concrete instance, evaluated independently of the lemma: `C(5, 3) = 10`.
example : ∑ ab ∈ antidiagonal 4, ab.1.choose 1 * ab.2.choose 1 = 10 := by decide

example : ∑ ab ∈ antidiagonal 4, ab.1.choose 1 * ab.2.choose 1 = 10 := by
  rw [Nat.sum_antidiagonal_choose_mul_choose]
  rfl

-- The `range` form agrees with direct evaluation: `C(6, 4) = 15`.
example : ∑ i ∈ range 6, i.choose 2 * (5 - i).choose 1 = 15 := by decide

example : ∑ i ∈ range 6, i.choose 2 * (5 - i).choose 1 = 15 := by
  rw [Nat.sum_range_choose_mul_choose_sub]
  rfl

-- When `p + q > n`, every summand and the right-hand side vanish.
example : ∑ i ∈ range 3, i.choose 2 * (2 - i).choose 1 = 0 := by
  rw [Nat.sum_range_choose_mul_choose_sub]
  rfl
