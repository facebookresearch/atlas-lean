/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.InverseColumns

/-! # Tests for `MathlibExt.NumberTheory.RepetendTable.InverseColumns` -/

namespace MathlibExtTest.RepetendTable.InverseColumns

open MetaMathlibExt

-- Test section: a concrete table. The bases of order `5` modulo `11` are `3`, `4`, `5` and `9`;
-- the order is computed through `orderOf_eq_iff`.
theorem rows_eleven :
    ((Finset.Ico 1 11).filter fun b => Nat.Coprime b 11 ∧ orderOf (b : ZMod 11) = 5) =
      {3, 4, 5, 9} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 11)) (by decide : 0 < 5)]
  decide

-- Modulo `5`, `2 * 3 ≡ 1` and `2 ^ 2 ≢ 1`, so columns `2` and `3` match.
example :
    let B := (Finset.Ico 1 11).filter fun b => Nat.Coprime b 11 ∧ orderOf (b : ZMod 11) = 5
    (B.val.map fun b => b ^ (2 + 1) / 11 % b) = B.val.map fun b => b ^ (3 + 1) / 11 % b :=
  repetend_column_eq_column_of_mul_modEq_one 11 5 2 3 (by decide) (by decide) (by decide)
    (by decide)

-- Column `2` reads `2, 1, 1, 3` down the rows and column `3` reads `1, 3, 1, 2`: the same
-- multiset in a different order.
example : ([3, 4, 5, 9].map fun b => b ^ (2 + 1) / 11 % b) = [2, 1, 1, 3] := by decide
example : ([3, 4, 5, 9].map fun b => b ^ (3 + 1) / 11 % b) = [1, 3, 1, 2] := by decide

-- Test section: boundary probes. Columns that are not inverse need not match: column `1` reads
-- `0, 1, 2, 7`, which is not column `2`.
example : ([3, 4, 5, 9].map fun b => b ^ (1 + 1) / 11 % b) = [0, 1, 2, 7] := by decide

example :
    let B := (Finset.Ico 1 11).filter fun b => Nat.Coprime b 11 ∧ orderOf (b : ZMod 11) = 5
    (B.val.map fun b => b ^ (1 + 1) / 11 % b) ≠ B.val.map fun b => b ^ (2 + 1) / 11 % b := by
  intro B
  rw [show B = {3, 4, 5, 9} from rows_eleven]
  decide

-- For `n ≤ 1` the table has no rows, and both columns are empty: first `n = 0`, then `n = 1`.
example (L j : ℕ) :
    let B := (Finset.Ico 1 0).filter fun b => Nat.Coprime b 0 ∧ orderOf (b : ZMod 0) = L
    (B.val.map fun b => b ^ (j + 1) / 0 % b) = 0 := by
  simp

example (L j : ℕ) :
    let B := (Finset.Ico 1 1).filter fun b => Nat.Coprime b 1 ∧ orderOf (b : ZMod 1) = L
    (B.val.map fun b => b ^ (j + 1) / 1 % b) = 0 := by
  simp

end MathlibExtTest.RepetendTable.InverseColumns
