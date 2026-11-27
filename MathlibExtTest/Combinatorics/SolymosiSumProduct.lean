/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SolymosiSumProduct

/-! # Tests for Solymosi's finite sum-product inequality -/

open MathlibExt.Combinatorics.RealSumProductExponentWanted
open scoped Pointwise

-- The logarithm vanishes on singletons, so the size restriction is sharp among nonempty sets.
example {A : Finset ℝ} (hA : A.Nonempty) :
    (Real.log 2 * (A.card : ℝ) ^ 4 ≤
      1296 * (A * A).card * (A + A).card ^ (2 : ℕ) * Real.log A.card) ↔ 2 ≤ A.card := by
  refine ⟨fun h => ?_, solymosi_sum_product A⟩
  by_contra! hsmall
  have hcard : A.card = 1 := by have := hA.card_pos; omega
  simp [hcard, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).not_ge] at h
