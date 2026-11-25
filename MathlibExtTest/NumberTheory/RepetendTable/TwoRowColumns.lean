/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.TwoRowColumns

/-! # Tests for `MathlibExt.NumberTheory.RepetendTable.TwoRowColumns` -/

namespace MathlibExtTest.RepetendTable.TwoRowColumns

open MetaMathlibExt

-- Test section: the two-row table of `n = 5` and `L = 4`. Its rows are `2` and `3`, the units of
-- order `4` modulo `5`; the order is computed through `orderOf_eq_iff`.
theorem rows_five :
    ((Finset.Ico 1 5).filter fun c => Nat.Coprime c 5 ∧ orderOf (c : ZMod 5) = 4) = {2, 3} := by
  rw [Finset.filter_congr fun (c : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (c : ZMod 5)) (by decide : 0 < 4)]
  decide

-- The table of `n = 11` and `L = 5` has the four rows `3`, `4`, `5` and `9`.
theorem rows_eleven :
    ((Finset.Ico 1 11).filter fun c => Nat.Coprime c 11 ∧ orderOf (c : ZMod 11) = 5) =
      {3, 4, 5, 9} := by
  rw [Finset.filter_congr fun (c : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (c : ZMod 11)) (by decide : 0 < 5)]
  decide

-- The rows hold the digits of `1/5` in bases `2` and `3`: `1/5 = 0.(0011)₂ = 0.(0121)₃`.
example : (List.range 4).map (fun k => 2 ^ (k + 1) / 5 % 2) = [0, 0, 1, 1] := by decide

example : (List.range 4).map (fun k => 3 ^ (k + 1) / 5 % 3) = [0, 1, 2, 1] := by decide

-- Test section: the hypotheses hold with `i ≠ j`. The digits of `1/5` repeat with period `L = 4`,
-- so columns `0` and `4` match, and the theorem gives `D_0 = ±D_4` and equal column sums.
example :
    let B := (Finset.Ico 1 5).filter fun c => Nat.Coprime c 5 ∧ orderOf (c : ZMod 5) = 4
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / 5 % c
    let D : ℕ → ℤ := fun k => ((3 ^ (k + 1) / 5 % 3 : ℕ) : ℤ) - (2 ^ (k + 1) / 5 % 2 : ℕ)
    (D 0 = D 4 ∨ D 0 = -D 4) ∧ (C 0).sum = (C 4).sum := by
  intro B C D
  refine repetend_digit_diff_of_columns_eq 5 4 2 3 0 4 ?_ ?_ ?_ (by decide) ?_ <;>
    simp only [rows_five] <;> decide

-- Test section: the contrapositive separates columns. In the table of `n = 5`, `D_0 = 0` and
-- `D_1 = 1` do not agree up to sign, so columns `0` and `1` differ.
example :
    let B := (Finset.Ico 1 5).filter fun c => Nat.Coprime c 5 ∧ orderOf (c : ZMod 5) = 4
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / 5 % c
    C 0 ≠ C 1 := by
  intro B C hC
  have h := (repetend_digit_diff_of_columns_eq 5 4 2 3 0 1 (by simp only [rows_five]; decide)
    (by simp only [rows_five]; decide) (by simp only [rows_five]; decide) (by decide) hC).1
  revert h
  decide

-- Test section: boundary probes. The two conclusions are independent: in the table of `n = 5`,
-- `D_1 = D_2 = 1`, yet columns `1` and `2` differ, since their sums are `1` and `3`.
example :
    let B := (Finset.Ico 1 5).filter fun c => Nat.Coprime c 5 ∧ orderOf (c : ZMod 5) = 4
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / 5 % c
    let D : ℕ → ℤ := fun k => ((3 ^ (k + 1) / 5 % 3 : ℕ) : ℤ) - (2 ^ (k + 1) / 5 % 2 : ℕ)
    D 1 = D 2 ∧ (C 1).sum = 1 ∧ (C 2).sum = 3 := by
  intro B C D
  simp only [B, C, D, rows_five]
  decide

-- Without `B.card = 2` the first conclusion fails. For `n = 11` and `L = 5` the table has the
-- four rows `3`, `4`, `5` and `9`, and columns `2` and `3` match, but the rows `b = 3` and `b' = 4`
-- give `D_2 = -1` and `D_3 = 2`.
example :
    let B := (Finset.Ico 1 11).filter fun c => Nat.Coprime c 11 ∧ orderOf (c : ZMod 11) = 5
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / 11 % c
    let D : ℕ → ℤ := fun k => ((4 ^ (k + 1) / 11 % 4 : ℕ) : ℤ) - (3 ^ (k + 1) / 11 % 3 : ℕ)
    B.card = 4 ∧ 3 ∈ B ∧ 4 ∈ B ∧ C 2 = C 3 ∧ ¬(D 2 = D 3 ∨ D 2 = -D 3) := by
  intro B C D
  simp only [B, C, D, rows_eleven]
  decide

end MathlibExtTest.RepetendTable.TwoRowColumns
