/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions

namespace MetaMathlibExt.DelannoyConstructions

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

end MetaMathlibExt.DelannoyConstructions
