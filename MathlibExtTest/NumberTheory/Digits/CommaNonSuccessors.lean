/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.CommaNonSuccessors

open MetaMathlibExt

-- In the smallest base, `18 = 2 · 3²` is not the comma successor of any positive integer.
example : ¬ ∃ k : ℕ, 0 < k ∧ IsCommaSucc 3 k 18 :=
  (not_commaSucc_iff 3 18 (by decide) (by decide)).2 ⟨2, 2, le_rfl, le_rfl, le_rfl, rfl⟩

-- `200 = 2 · 10²` is a comma-child of 118, but the comma successor of 118 is its smaller
-- child 199, and `200` is the comma successor of no positive integer.
example : IsCommaSucc 10 118 199 ∧ ¬ ∃ k : ℕ, 0 < k ∧ IsCommaSucc 10 k 200 := by
  refine ⟨?_, (not_commaSucc_iff 10 200 (by decide) (by decide)).2
    ⟨2, 2, le_rfl, le_rfl, by decide, by decide⟩⟩
  unfold IsCommaSucc IsCommaCandidate commaMsd
  decide

-- At the threshold, `99 = 10² - 1` is a comma successor: of 90, as a direct computation shows.
example : (∃ k : ℕ, 0 < k ∧ IsCommaSucc 10 k 99) ∧ IsCommaSucc 10 90 99 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    obtain ⟨c, i, hi, hc, -, h99⟩ := (not_commaSucc_iff 10 99 (by decide) le_rfl).1 h
    have : 2 * 10 ^ 2 ≤ c * 10 ^ i := Nat.mul_le_mul hc (Nat.pow_le_pow_right (by decide) hi)
    omega
  · unfold IsCommaSucc IsCommaCandidate commaMsd
    decide

-- The leading digit must be at least 2: `1000 = 1 · 10³` is a comma successor (of 909).
example : (∃ k : ℕ, 0 < k ∧ IsCommaSucc 10 k 1000) ∧ IsCommaSucc 10 909 1000 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    obtain ⟨c, i, hi, hc, hc9, h1000⟩ := (not_commaSucc_iff 10 1000 (by decide) (by decide)).1 h
    rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · obtain rfl : i = 2 := by omega
      omega
    · have : c * 10 ^ 3 ≤ c * 10 ^ i :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by decide) hi3)
      omega
  · unfold IsCommaSucc IsCommaCandidate commaMsd
    decide
