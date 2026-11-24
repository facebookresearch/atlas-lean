/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual cyclic descent counts

The count includes the closing edge of the original permutation word.
For a one-letter word it is zero. Rotating positions reindexes the same
edges, and rotating values removes one maximal-value descent and adds one
minimal-value descent. The latter proof is an actual integer indicator
identity, so no cyclic-invariance or coefficient-count certificate is used.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- The actual number of descents in the original cyclic permutation word. -/
def cyclicDescentNumber {n : ℕ} (σ : Perm (Fin (n + 1))) : ℕ :=
  ∑ i : Fin (n + 1), if σ (finRotate (n + 1) i) < σ i then 1 else 0

private theorem rotation_indicator {n : ℕ} (a b : Fin (n + 1)) :
    (if finRotate (n + 1) b < finRotate (n + 1) a then (1 : ℤ) else 0) =
      (if b < a then (1 : ℤ) else 0) - (if a = Fin.last n then 1 else 0) +
        (if b = Fin.last n then 1 else 0) := by
  by_cases ha : a = Fin.last n
  · subst a
    by_cases hb : b = Fin.last n
    · subst b
      simp only [finRotate_last, lt_irrefl, ite_false, ite_true]
      omega
    · have hb' : b.val < n := by
        have hne : b.val ≠ n := fun h => hb (Fin.ext h)
        omega
      rw [finRotate_last, finRotate_of_lt hb']
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_mk, Fin.val_last, hb', ite_false,
        ite_true, Nat.not_lt_zero, zero_sub, sub_self, add_zero, hb]
  · have ha' : a.val < n := by
      have hne : a.val ≠ n := fun h => ha (Fin.ext h)
      omega
    by_cases hb : b = Fin.last n
    · subst b
      rw [finRotate_last, finRotate_of_lt ha']
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_mk, Fin.val_last, ha, ite_false,
        ite_true, Nat.zero_lt_succ, sub_zero, zero_add]
      rw [ite_eq_right (by omega : ¬ n < a.val)]
      omega
    · have hb' : b.val < n := by
        have hne : b.val ≠ n := fun h => hb (Fin.ext h)
        omega
      rw [finRotate_of_lt ha', finRotate_of_lt hb']
      simp only [Fin.lt_def, Fin.val_mk, Nat.add_lt_add_iff_right, ha, hb,
        ite_false, sub_zero, add_zero]

/-- Rotating the original values preserves the actual cyclic descent count. -/
theorem cyclicDescentNumber_rotate_values {n : ℕ} (σ : Perm (Fin (n + 1))) :
    cyclicDescentNumber (finRotate (n + 1) * σ) = cyclicDescentNumber σ := by
  classical
  have hcast (s : Perm (Fin (n + 1))) :
      (cyclicDescentNumber s : ℤ) =
        ∑ i : Fin (n + 1), if s (finRotate (n + 1) i) < s i then (1 : ℤ) else 0 := by
    rw [cyclicDescentNumber, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  apply Nat.cast_injective (R := ℤ)
  rw [hcast, hcast]
  change (∑ i : Fin (n + 1),
      if finRotate (n + 1) (σ (finRotate (n + 1) i)) < finRotate (n + 1) (σ i) then (1 : ℤ) else 0) =
    ∑ i : Fin (n + 1), if σ (finRotate (n + 1) i) < σ i then (1 : ℤ) else 0
  simp_rw [rotation_indicator]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h := Equiv.sum_comp (finRotate (n + 1))
    (fun i : Fin (n + 1) => if σ i = Fin.last n then (1 : ℤ) else 0)
  rw [h]
  omega

/-- Every actual value-rotation power preserves the original cyclic descent count. -/
theorem cyclicDescentNumber_rotate_values_pow {n : ℕ} (σ : Perm (Fin (n + 1))) (r : ℕ) :
    cyclicDescentNumber (finRotate (n + 1) ^ r * σ) = cyclicDescentNumber σ := by
  induction r with
  | zero => simp only [pow_zero, one_mul]
  | succ r hr =>
    rw [pow_succ', mul_assoc, cyclicDescentNumber_rotate_values, hr]

/-- Rotating the original positions reindexes the same cyclic edges. -/
theorem cyclicDescentNumber_rotate_positions_pow {n : ℕ} (σ : Perm (Fin (n + 1))) (r : ℕ) :
    cyclicDescentNumber (σ * finRotate (n + 1) ^ r) = cyclicDescentNumber σ := by
  have hcomm (i : Fin (n + 1)) :
      (finRotate (n + 1) ^ r) (finRotate (n + 1) i) =
        finRotate (n + 1) ((finRotate (n + 1) ^ r) i) := by
    have h : finRotate (n + 1) ^ r * finRotate (n + 1) =
        finRotate (n + 1) * finRotate (n + 1) ^ r := by
      rw [← pow_succ, ← pow_succ']
    exact congrArg (fun p : Perm (Fin (n + 1)) => p i) h
  simp only [cyclicDescentNumber, Equiv.Perm.mul_apply, hcomm]
  exact Equiv.sum_comp (finRotate (n + 1) ^ r)
    (fun i : Fin (n + 1) => if σ (finRotate (n + 1) i) < σ i then 1 else 0)

/-- Both original value and position rotations preserve the actual cyclic count. -/
theorem cyclicDescentNumber_two_sided {n : ℕ}
    (σ : Perm (Fin (n + 1))) (r s : ℕ) :
    cyclicDescentNumber (finRotate (n + 1) ^ r * σ * finRotate (n + 1) ^ s) =
      cyclicDescentNumber σ := by
  rw [cyclicDescentNumber_rotate_positions_pow, cyclicDescentNumber_rotate_values_pow]

end Equiv.Perm
