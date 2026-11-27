/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangular

/-! # Tests for representations by coprime pairs and reduced triangular triples -/

open MetaMathlibExt

-- At n = 2 the triple (3, 6, 10) reduces to (3, 3, 5).
-- Below the first generator, every representation has first coefficient zero.
example (m : ℕ) (hm : m < 3) :
    frobeniusRepCount ![3, 3, 5] m = frobeniusRepCount ![3, 5] m := by
  have h := frobeniusRepCount_triangular_reduced_eq_sum 2 (by decide) m
  change frobeniusRepCount ![3, 3, 5] m = ∑ j ∈ Finset.range (m / 3 + 1),
    frobeniusRepCount ![3, 5] ((m : ℤ) - j * 3) at h
  simpa [Nat.div_eq_of_lt hm] using h

-- At the first multiple of 3, the last summand counts a representation of zero.
example : frobeniusRepCount ![3, 3, 5] 3 =
    frobeniusRepCount ![3, 5] 3 + frobeniusRepCount ![3, 5] 0 := by
  have h := frobeniusRepCount_triangular_reduced_eq_sum 2 (by decide) 3
  change frobeniusRepCount ![3, 3, 5] 3 = ∑ j ∈ Finset.range 2,
    frobeniusRepCount ![3, 5] (3 - (j : ℤ) * 3) at h
  simpa [Finset.sum_range_succ] using h

namespace MetaMathlibExt.frobeniusRepCount_pair_sub_ge

private theorem two_three_frobenius : IsGenFrobeniusNumber ![2, 3] 0 1 := by
  simp only [IsGenFrobeniusNumber, frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_ofNat, Nat.cast_zero, nonpos_iff_eq_zero, Set.encard_eq_zero,
    Set.eq_empty_iff_forall_notMem, Set.encard_pos]
  constructor
  · intro x (hx : (x 0 : ℤ) * 2 + (x 1 : ℤ) * 3 = 1)
    omega
  · intro m hm
    refine ⟨![(m / 2 - m % 2).toNat, (m % 2).toNat], ?_⟩
    change ((m / 2 - m % 2).toNat : ℤ) * 2 + ((m % 2).toNat : ℤ) * 3 = m
    omega

-- The gap is one, which itself has no representation by 2 and 3.
example : frobeniusRepCount ![2, 3] 5 ≤ frobeniusRepCount ![2, 3] 6 := by
  exact frobeniusRepCount_pair_sub_ge 2 3 (by decide) (by decide) (by decide)
    0 3 1 two_three_frobenius 8 (by decide) 1

-- With j > k the shifted Frobenius argument can cross zero.
example : frobeniusRepCount ![2, 3] (-1) ≤ frobeniusRepCount ![2, 3] 0 := by
  exact frobeniusRepCount_pair_sub_ge 2 3 (by decide) (by decide) (by decide)
    0 0 1 two_three_frobenius 2 (by decide) 1

end MetaMathlibExt.frobeniusRepCount_pair_sub_ge

private theorem countOneOne (m : ℕ) : frobeniusRepCount ![1, 1] m = m + 1 := by
  simp only [frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_one, mul_one]
  rw [← ENat.card_coe_set_eq]
  let e : {x : Fin 2 → ℕ | (x 0 : ℤ) + (x 1 : ℤ) = m} ≃ Fin (m + 1) :=
    { toFun := fun x => ⟨x.val 0, by have hx := x.property; change _ + _ = (m : ℤ) at hx; omega⟩
      invFun := fun i => ⟨![(i : ℕ), m - (i : ℕ)], by
        change ((i : ℕ) : ℤ) + ((m - (i : ℕ) : ℕ) : ℤ) = m
        have hi := i.isLt
        omega⟩
      left_inv := fun x => Subtype.ext (funext (Fin.forall_fin_two.mpr ⟨rfl, by
        have hx := x.property
        change (x.val 0 : ℤ) + (x.val 1 : ℤ) = m at hx
        change m - x.val 0 = x.val 1
        omega⟩))
      right_inv := fun _ => rfl }
  rw [ENat.card_congr e]
  simp

private theorem oneOneFrobenius (r : ℕ) : IsGenFrobeniusNumber ![1, 1] r ((r : ℤ) - 1) := by
  constructor
  · cases r with
    | zero => rw [frobeniusRepCount_eq_zero_of_neg _ (by omega)]; exact le_rfl
    | succ r =>
      rw [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega, countOneOne, Nat.cast_succ]
  · intro m hm
    have hm0 : 0 ≤ m := by omega
    rw [← Int.toNat_of_nonneg hm0, countOneOne, ← Nat.cast_one, ← Nat.cast_add,
      ENat.natCast_lt_natCast]
    omega

-- A negative shift can fall below zero, where the lower cutoff is omitted.
example : frobeniusRepCount ![1, 1] (-2) = 0 := by
  apply (frobeniusRepCount_pair_eq_iff 1 1 (by decide) (by decide) (by decide)
    (fun r => (r : ℤ) - 1) oneOneFrobenius 0 0 1 (by decide) (Or.inl (by decide)) (-1)).2
  norm_num

-- At the upper endpoint the count is exactly the requested positive level.
example : frobeniusRepCount ![1, 1] 2 = 3 := by
  apply (frobeniusRepCount_pair_eq_iff 1 1 (by decide) (by decide) (by decide)
    (fun r => (r : ℤ) - 1) oneOneFrobenius 3 1 1 (by decide) (Or.inr (by decide)) 2).2
  norm_num
