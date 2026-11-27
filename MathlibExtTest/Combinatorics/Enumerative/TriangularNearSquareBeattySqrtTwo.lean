/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.TriangularNearSquareBeattySqrtTwo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.NatSqrt

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.TriangularNearSquareBeattySqrtTwo` -/

namespace MathlibExtTest.TriangularNearSquareBeattySqrtTwo

open MetaMathlibExt

/-- `⌊n√2⌋` is the integer square root of `2n²`, which `norm_num` evaluates. -/
private theorem floor_eq_sqrt (n : ℕ) : ⌊(n : ℝ) * Real.sqrt 2⌋₊ = Nat.sqrt (2 * n ^ 2) := by
  rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n), mul_comm]

/-- No square lies strictly between `b ^ 2` and `(b + 1) ^ 2`. -/
private theorem sq_le_or_le_sq (k : ℤ) (b : ℕ) : k ^ 2 ≤ b ^ 2 ∨ (b + 1) ^ 2 ≤ k ^ 2 := by
  rcases le_or_gt |k| b with h | h
  · exact Or.inl (by nlinarith [sq_abs k, abs_nonneg k])
  · exact Or.inr (by nlinarith [sq_abs k])

-- The first terms of `⌊n√2⌋` (A001951).
example : (List.range 11).map (fun n : ℕ => ⌊(n : ℝ) * Real.sqrt 2⌋₊) =
    [0, 1, 2, 4, 5, 7, 8, 9, 11, 12, 14] := by
  norm_num [List.range_succ, floor_eq_sqrt]

-- At `n = 5`: `a = 7`, so some square is within `⌊7/2⌋ = 3` of `T_7 = 28`.
example : ∃ k : ℤ, |28 - k ^ 2| ≤ 3 := by
  have h := exists_sq_near_triangular_beatty_sqrt_two 5
  rw [floor_eq_sqrt] at h
  norm_num at h
  exact h

-- The bound is attained at `n = 5`: the nearest square to `28` is `25`, at distance `3`.
example (k : ℤ) : 3 ≤ |28 - k ^ 2| := by
  rw [le_abs]
  rcases sq_le_or_le_sq k 5 with h | h <;> push_cast at h <;> omega

-- At `n = 12`: `a = 16`, so some square is within `⌊16/2⌋ = 8` of `T_16 = 136`.
example : ∃ k : ℤ, |136 - k ^ 2| ≤ 8 := by
  have h := exists_sq_near_triangular_beatty_sqrt_two 12
  rw [floor_eq_sqrt] at h
  norm_num at h
  exact h

-- The bound is attained at `n = 12`, now from above: the nearest square to `136` is `144`.
example (k : ℤ) : 8 ≤ |136 - k ^ 2| := by
  rw [le_abs]
  rcases sq_le_or_le_sq k 11 with h | h <;> push_cast at h <;> omega

-- The bound fails for other `a`: `T_3 = 6` is at distance `2 > ⌊3/2⌋` from every square. So the
-- theorem shows that `⌊n√2⌋` never equals `3`.
example (n : ℕ) : ⌊(n : ℝ) * Real.sqrt 2⌋₊ ≠ 3 := by
  intro ha
  obtain ⟨k, hk⟩ := exists_sq_near_triangular_beatty_sqrt_two n
  rw [ha] at hk
  norm_num at hk
  rw [abs_le] at hk
  rcases sq_le_or_le_sq k 2 with h | h <;> push_cast at h <;> omega

end MathlibExtTest.TriangularNearSquareBeattySqrtTwo
