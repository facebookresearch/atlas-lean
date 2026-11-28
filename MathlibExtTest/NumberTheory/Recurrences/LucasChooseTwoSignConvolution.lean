/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasChooseTwoSignConvolution

/-! # Tests for the Lucas binomial sums with triangular-number signs -/

open Finset MetaMathlibExt

-- Independently evaluate both orientations and the closed form at `p = 2`, `n = 1`.
-- This gives a negative result and exercises all four residues of the summation index.
example :
    (∑ k ∈ range (4 * 1 + 2),
      ((4 * 1 + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
        lucasU ⟨2, -1, by decide⟩ k * lucasV ⟨2, -1, by decide⟩ (4 * 1 + 1 - k)) = -232 ∧
    (∑ k ∈ range (4 * 1 + 2),
      ((4 * 1 + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
        lucasV ⟨2, -1, by decide⟩ k * lucasU ⟨2, -1, by decide⟩ (4 * 1 + 1 - k)) = -232 ∧
    (-1 : ℤ) ^ (1 : ℕ) * 2 ^ (2 * 1 + 1 : ℕ) * lucasU ⟨2, -1, by decide⟩ (4 * 1 + 1) = -232 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

-- A client uses both projections at the endpoint `n = 0`.
example :
    (∑ k ∈ range (4 * 0 + 2),
      ((4 * 0 + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
        lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (4 * 0 + 1 - k)) = 2 ∧
    (∑ k ∈ range (4 * 0 + 2),
      ((4 * 0 + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
        lucasV ⟨-2, -1, by decide⟩ k * lucasU ⟨-2, -1, by decide⟩ (4 * 0 + 1 - k)) = 2 := by
  have h := lucasU_lucasV_sum_choose_sign_choose_two (-2) 0
  exact ⟨h.1.trans (by decide +kernel), h.2.trans (by decide +kernel)⟩
