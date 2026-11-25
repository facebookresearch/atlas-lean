/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingFloorSqrtSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum.NatSqrt

/-! # Tests for the alternating sum of floors of square roots -/

open MathlibExt.NumberTheory.AlternatingFloorSqrtSumWanted

-- The singleton interval contributes its positive endpoint.
example : (∑ j ∈ Finset.Icc 1 1, (-1 : ℤ) ^ (j + 1) * (Nat.sqrt (j * 1) : ℤ)) = 1 := by
  decide

-- An odd composite with perfect squares among the interior radicands.
example : (∑ j ∈ Finset.Icc 1 9, (-1 : ℤ) ^ (j + 1) * (Nat.sqrt (j * 9) : ℤ)) = 5 :=
  alternating_sum_floor_sqrt_mul (n := 9) (by decide) ⟨4, rfl⟩

-- At the first positive even index the alternating sum is negative.
example : (∑ j ∈ Finset.Icc 1 2, (-1 : ℤ) ^ (j + 1) * (Nat.sqrt (j * 2) : ℤ)) = -1 := by
  rw [Finset.sum_Icc_succ_top (show 1 ≤ 1 + 1 by decide), Finset.Icc_self, Finset.sum_singleton]
  norm_num
