/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTableRepetendColumnsNeOfThreePowOfSix

/-!
# Tests for distinct columns in order-six repetend tables

The theorem separates columns with equal sums at moduli nine and eighteen.
-/

namespace MathlibExtTest.NumberTheory.RepetendTableRepetendColumnsNeOfThreePowOfSix

private theorem rows_nine :
    ((Finset.Ico 1 9).filter fun b => Nat.Coprime b 9 ∧ orderOf (b : ZMod 9) = 6) = {2, 5} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 9)) (by decide : 0 < 6)]
  decide

private theorem rows_eighteen :
    ((Finset.Ico 1 18).filter fun b => Nat.Coprime b 18 ∧ orderOf (b : ZMod 18) = 6) = {5, 11} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 18)) (by decide : 0 < 6)]
  decide

example :
    ({2 ^ 2 / 9 % 2, 5 ^ 2 / 9 % 5} : Multiset ℕ) ≠ {2 ^ 6 / 9 % 2, 5 ^ 6 / 9 % 5} := by
  have h := MetaMathlibExt.repetend_columns_ne_of_three_pow_of_six 2 1 (by decide)
    (Or.inl rfl) 1 (by decide) 5 (by decide) (by decide)
  simpa [rows_nine] using h

example :
    ({5 ^ 2 / 18 % 5, 11 ^ 2 / 18 % 11} : Multiset ℕ) ≠
      {5 ^ 5 / 18 % 5, 11 ^ 5 / 18 % 11} := by
  have h := MetaMathlibExt.repetend_columns_ne_of_three_pow_of_six 2 2 (by decide)
    (Or.inr rfl) 1 (by decide) 4 (by decide) (by decide)
  simpa [rows_eighteen] using h

end MathlibExtTest.NumberTheory.RepetendTableRepetendColumnsNeOfThreePowOfSix
