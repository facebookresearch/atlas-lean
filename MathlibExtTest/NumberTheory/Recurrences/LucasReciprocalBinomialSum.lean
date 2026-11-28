/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasReciprocalBinomialSum

/-! # Tests for the alternating reciprocal-binomial Lucas sum -/

open Finset MetaMathlibExt

-- With `p = 1` and `n = 1`, the three summands are `0`, `-1/8`, and `1/3`.
-- Evaluate the sum and the closed form separately, without the new theorem.
example :
    (∑ k ∈ range (2 * 1 + 1),
        ((2 * 1).choose k : ℚ) / ((4 * 1).choose k * (4 * 1).choose (2 * 1 + k)) * (-1) ^ k *
          lucasU ⟨1, -1, by decide⟩ k * lucasV ⟨1, -1, by decide⟩ (2 * 1 - k)) = 5 / 24 ∧
      (4 * 1 + 1 : ℚ) / (3 * 1 + 1) / (4 * 1).choose (2 * 1) *
        lucasU ⟨1, -1, by decide⟩ (2 * 1) = 5 / 24 := by
  constructor <;> decide +kernel

-- At `n = 0`, both the sole summand and the closed form vanish.
example :
    (∑ k ∈ range (2 * 0 + 1),
        ((2 * 0).choose k : ℚ) / ((4 * 0).choose k * (4 * 0).choose (2 * 0 + k)) * (-1) ^ k *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 * 0 - k)) = 0 ∧
      (4 * 0 + 1 : ℚ) / (3 * 0 + 1) / (4 * 0).choose (2 * 0) *
        lucasU ⟨-2, -1, by decide⟩ (2 * 0) = 0 := by
  constructor <;> decide +kernel

-- Use the public theorem at negative `p`, where `U₄ = -12`.
example :
    ∑ k ∈ range (2 * 2 + 1),
        ((2 * 2).choose k : ℚ) / ((4 * 2).choose k * (4 * 2).choose (2 * 2 + k)) * (-1) ^ k *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 * 2 - k) = -54 / 245 := by
  rw [lucasU_lucasV_sum_choose_inv_alternating]
  decide +kernel
