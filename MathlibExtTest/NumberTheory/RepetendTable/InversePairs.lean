/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.InversePairs

/-! # Tests for `MathlibExt.NumberTheory.RepetendTable.InversePairs` -/

namespace MathlibExtTest.RepetendTable.InversePairs

open MetaMathlibExt

-- Test section: concrete tables; the order is computed through `orderOf_eq_iff`. The bases of
-- order `3` modulo `7` are `2` and its inverse `4`.
theorem rows_seven :
    ((Finset.Ico 1 7).filter fun b => Nat.Coprime b 7 ∧ orderOf (b : ZMod 7) = 3) = {2, 4} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 7)) (by decide : 0 < 3)]
  decide

example :
    Even ((Finset.Ico 1 7).filter fun b => Nat.Coprime b 7 ∧ orderOf (b : ZMod 7) = 3).card :=
  even_card_small_bases_orderOf 7 3 (by decide)

-- The unit group modulo `15` is not cyclic. Its bases of order `4` form the two inverse pairs
-- `2 · 8 ≡ 1` and `7 · 13 ≡ 1 (mod 15)`.
theorem rows_fifteen :
    ((Finset.Ico 1 15).filter fun b => Nat.Coprime b 15 ∧ orderOf (b : ZMod 15) = 4) =
      {2, 7, 8, 13} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 15)) (by decide : 0 < 4)]
  decide

example : (2 * 8 : ZMod 15) = 1 ∧ (7 * 13 : ZMod 15) = 1 := by decide

example :
    Even ((Finset.Ico 1 15).filter fun b => Nat.Coprime b 15 ∧ orderOf (b : ZMod 15) = 4).card :=
  even_card_small_bases_orderOf 15 4 (by decide)

-- Test section: a consequence. For `L > 2`, no modulus has exactly one base of order `L`.
example (n L : ℕ) (hL : 2 < L) :
    ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L).card ≠ 1 :=
  fun h => Nat.not_even_one (h ▸ even_card_small_bases_orderOf n L hL)

-- Test section: boundary probes. The hypothesis `2 < L` is needed: modulo `8` the three bases
-- `3`, `5` and `7` have order `2`, and each is its own inverse.
theorem rows_eight :
    ((Finset.Ico 1 8).filter fun b => Nat.Coprime b 8 ∧ orderOf (b : ZMod 8) = 2) = {3, 5, 7} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 8)) (by decide : 0 < 2)]
  decide

example :
    ¬ Even ((Finset.Ico 1 8).filter fun b => Nat.Coprime b 8 ∧ orderOf (b : ZMod 8) = 2).card := by
  rw [rows_eight]
  decide

-- For `L = 1` the only base is `1`, its own inverse.
example :
    ((Finset.Ico 1 7).filter fun b => Nat.Coprime b 7 ∧ orderOf (b : ZMod 7) = 1) = {1} := by
  rw [Finset.filter_congr fun (b : ℕ) _ => and_congr_right_iff.mpr fun _ =>
    orderOf_eq_iff (x := (b : ZMod 7)) (by decide : 0 < 1)]
  decide

-- For `n = 0` and `n = 1` there are no bases at all.
example (L : ℕ) :
    ((Finset.Ico 1 0).filter fun b => Nat.Coprime b 0 ∧ orderOf (b : ZMod 0) = L) = ∅ := by
  simp

example (L : ℕ) :
    ((Finset.Ico 1 1).filter fun b => Nat.Coprime b 1 ∧ orderOf (b : ZMod 1) = L) = ∅ := by
  simp

end MathlibExtTest.RepetendTable.InversePairs
