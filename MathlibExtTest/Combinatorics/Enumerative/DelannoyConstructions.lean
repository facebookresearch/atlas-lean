/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions

namespace MetaMathlibExt.DelannoyConstructions

open Finset

-- With k = 0 the two index conventions give the same nontrivial sum.
example : genDelannoyLower 0 2 2 = 13 ∧ genDelannoyUpper 0 2 2 = 13 ∧
    (∑ j ∈ Ico 0 (min 2 2 + 1), (2 : ℕ).choose (j - 0) * (2 : ℕ).choose j * 2 ^ j) = 13 ∧
    (∑ j ∈ range (min 2 2 + 1), (2 : ℕ).choose (j + 0) * (2 : ℕ).choose j * 2 ^ j) = 13 := by
  decide

-- The upper formula uses j + k in the first binomial and stops at n when n < m.
example : genDelannoyUpper 1 3 2 = 44 ∧
    (∑ j ∈ range (min 3 2 + 1), (3 + 1).choose (j + 1) * (2 : ℕ).choose j * 2 ^ j) = 44 := by
  decide

-- The lower formula starts at k, not zero, and includes j = min m n.
example : genDelannoyLower 1 2 2 = 8 ∧
    (∑ j ∈ Ico 1 (min 2 2 + 1), (2 - 1).choose (j - 1) * (2 : ℕ).choose j * 2 ^ j) = 8 := by
  decide

-- At m = k < n the lower sum has exactly one term; the upper sum also stops at m.
example : genDelannoyLower 1 1 3 = 6 ∧
    (∑ j ∈ Ico 1 (min 1 3 + 1), (1 - 1).choose (j - 1) * (3 : ℕ).choose j * 2 ^ j) = 6 ∧
    genDelannoyUpper 1 1 3 = 8 ∧
    (∑ j ∈ range (min 1 3 + 1), (1 + 1).choose (j + 1) * (3 : ℕ).choose j * 2 ^ j) = 8 := by
  decide

-- Reindexing the lower formula gives the two terms at j = 0 and j = 1.
example : genDelannoyLower 1 2 4 = 32 ∧
    (∑ j ∈ range (min (2 - 1) (4 - 1) + 1),
      (2 - 1).choose j * (4 : ℕ).choose (j + 1) * 2 ^ (j + 1)) = 32 := by
  decide

-- The named corollaries give the two entries at m = k < n.
example : genDelannoyLower 1 1 3 + genDelannoyUpper 1 1 3 = 14 := by
  rw [genDelannoyLower_eq_sum_two_pow 1 1 3 (by decide) (by decide),
    genDelannoyUpper_eq_sum_two_pow 1 1 3]
  decide

-- A client can use either component of the unified theorem from this import.
example : genDelannoyLower 1 2 2 = genDelannoyUpper 1 1 3 := by
  rw [(genDelannoy_eq_sum_two_pow_unified 1 2 2).1 (by decide) (by decide),
    (genDelannoy_eq_sum_two_pow_unified 1 1 3).2]
  decide

-- At the boundary n = 0, the formula has only its constant term.
example (m : ℕ) : ordinaryRiordanPascalLikeMatrix m m 1 = 1 := by
  simpa using delannoy_eq_sum_choose_mul_choose_two_pow m 0

-- With m > n, the right-hand sum stops strictly before the triangle entry's sum.
example : ordinaryRiordanPascalLikeMatrix 5 3 1 = 25 := by
  rw [delannoy_eq_sum_choose_mul_choose_two_pow 3 2]
  decide +kernel

-- Independently evaluate the original entry with the two coordinates reversed.
example : ordinaryRiordanPascalLikeMatrix 5 2 1 = 25 := by
  decide +kernel

-- On row zero only the initial summand contributes.
example : genDelannoyUpper 3 0 4 = 1 := by decide

-- In column zero the sum has a single binomial coefficient.
example (k m : ℕ) : (m + k).choose k + genDelannoyUpper k m 1 =
    2 * (m + (k + 1)).choose (k + 1) := by
  simpa [genDelannoyUpper] using genDelannoyUpper_add_succ_right k m 0

-- For a positive upper index, the adjacent entries 33 and 51 sum to twice 42.
example : genDelannoyUpper 1 2 3 + genDelannoyUpper 1 2 4 = 84 := by
  rw [genDelannoyUpper_add_succ_right 1 2 3]
  decide

-- The smallest positive upper index and the origin give 1 + 2 = 3.
example : genDelannoyUpper 1 0 0 + genDelannoyUpper 1 1 0 = 3 := by
  rw [genDelannoyUpper_add_succ_left 1 0 0 le_rfl]
  decide

-- The two upper-index-two entries are 14 and 30; their sum is D^1(3, 2).
example : genDelannoyUpper 2 2 1 + genDelannoyUpper 2 3 1 = 44 := by
  rw [genDelannoyUpper_add_succ_left 2 2 1 (by decide)]
  decide

-- At the least positive upper index, the difference gives the index-zero family.
example (m n : ℕ) : (genDelannoyUpper 1 (m + 1) n : ℤ) - genDelannoyUpper 1 m n =
    genDelannoyUpper 0 (m + 1) n :=
  genDelannoyUpper_succ_left_sub 1 m n le_rfl

-- The adjacent entries 14 and 30 have difference 16, the index-one entry at (3, 1).
example : (genDelannoyUpper 2 3 1 : ℤ) - genDelannoyUpper 2 2 1 = 16 := by
  rw [genDelannoyUpper_succ_left_sub 2 2 1 (by decide)]
  decide

-- At the first positive row and column zero, the difference is always two.
example (k : ℕ) : (genDelannoyUpper k 1 1 : ℤ) - genDelannoyUpper k 1 0 = 2 := by
  rw [genDelannoyUpper_succ_right_sub k 1 0 le_rfl]
  simp [genDelannoyUpper]

-- The adjacent entries 33 and 51 have difference 18.
example : (genDelannoyUpper 1 2 4 : ℤ) - genDelannoyUpper 1 2 3 = 18 := by
  rw [genDelannoyUpper_succ_right_sub 1 2 3 (by decide)]
  decide

-- At the lower family's boundary m = n = k, the first binomial factor is always one.
example : genDelannoyLower 3 3 3 = 8 := by decide

-- At the first positive column, the sum of consecutive natural numbers is odd.
example (n : ℕ) : n + (n + 1) ≡ 1 [MOD 2] := by
  simpa using choose_add_choose_succ_modEq_two n 1 le_rfl

-- Allowing column zero would give the wrong parity because natural subtraction truncates.
example : ¬ ((0 : ℕ).choose 0 + (0 + 1).choose 0 ≡ (0 : ℕ).choose (0 - 1) [MOD 2]) := by
  decide

-- Use a negative first-column value of opposite parity to the value at the origin.
private def seededArray (k : ℕ) : ℕ → ℕ → ℤ
  | 0 => fun n => (k + n).choose k
  | m + 1 => Nat.rec (-2) (fun n prev => seededArray k m (n + 1) + prev + seededArray k m n)

-- Before summing, consecutive rows can have opposite parity in column zero.
example : ¬ seededArray 2 0 0 ≡ seededArray 2 1 0 [ZMOD 2] := by decide

-- After one sum every row is odd in column one, where the top row sums to nine.
example (m : ℕ) : seededArray 2 m 1 + seededArray 2 m 2 ≡ 1 [ZMOD 2] := by
  have h := delannoyArray_horizontalSum_rows_modEq (seededArray 2) (fun _ _ => rfl) 1 le_rfl m 0 1
  exact h.trans (by decide)

-- For k = 0 a single horizontal sum is already even in every row.
example (m n : ℕ) : (2 : ℤ) ∣ seededArray 0 m n + seededArray 0 m (n + 1) :=
  (delannoyArray_binomial_seeds_parity (seededArray 0) (fun _ _ => rfl) 0 (fun _ => rfl)).1 m n

-- For k = 2 the first horizontal sum is even at the origin and odd one column later.
example : let row := seededArray 2 0
    (2 : ℤ) ∣ row 0 + row 1 ∧ ¬ (2 : ℤ) ∣ row 1 + row 2 := by decide

-- At the least admissible seed index, every horizontal sum is odd.
example (m n : ℕ) : seededArray 1 m n + seededArray 1 m (n + 1) ≡ 1 [ZMOD 2] := by
  simpa using delannoyArray_binomial_seeds_horizontalSum_modEq (seededArray 1)
    (fun _ _ => rfl) 1 le_rfl (fun _ => rfl) m n

-- With seed index two, the first horizontal sum in column zero is even in every row.
example (m : ℕ) : (2 : ℤ) ∣ seededArray 2 m 0 + seededArray 2 m 1 := by
  have h := delannoyArray_binomial_seeds_horizontalSum_modEq (seededArray 2)
    (fun _ _ => rfl) 2 (by decide) (fun _ => rfl) m 0
  exact h.dvd_iff.mpr (by decide)

local notation "H" => (fun S : ℕ → ℕ → ℤ => fun m n => S m n + S m (n + 1))

-- With zero seed index, three sums give a sharp uniform factor of eight.
example : (∀ m n, (8 : ℤ) ∣ H^[3] (seededArray 0) m n) ∧
    ∃ m n, ¬ (16 : ℤ) ∣ H^[3] (seededArray 0) m n :=
  delannoyArray_binomial_seeds_two_pow_dvd (seededArray 0) (fun _ _ => rfl) 0 3
    (by decide) (fun _ => rfl)

-- For positive seed index, the origin need not witness sharpness.
example : (4 : ℤ) ∣ H^[2] (seededArray 1) 0 0 ∧
    ¬ (4 : ℤ) ∣ H^[2] (seededArray 1) 1 0 := by decide

-- Three extra sums give a uniform factor of eight, but not sixteen.
example : (∀ m n, (8 : ℤ) ∣ H^[5] (seededArray 2) m n) ∧
    ∃ m n, ¬ (16 : ℤ) ∣ H^[5] (seededArray 2) m n :=
  delannoyArray_binomial_seeds_two_pow_dvd (seededArray 2) (fun _ _ => rfl) 2 3
    (by decide) (fun _ => rfl)

end MetaMathlibExt.DelannoyConstructions
