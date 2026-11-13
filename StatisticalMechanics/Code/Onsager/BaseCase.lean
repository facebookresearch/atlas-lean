/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Mathlib

namespace StatMech.Onsager.BaseCase

open Finset
open Fin.NatCast


def stepOf : Fin 4 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)


def pos {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (k : Fin n) : ℤ × ℤ :=
  ∑ i ∈ Finset.filter (· < k) Finset.univ, stepOf (d i)


def cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d (i + 1) - d i = 1)).card




theorem sum_shift {n : ℕ} [NeZero n] (d : Fin n → Fin 4) :
    (∑ i : Fin n, d (i + 1)) = ∑ i : Fin n, d i :=
  Equiv.sum_comp (Equiv.addRight (1 : Fin n)) d


theorem sum_turns_zero {n : ℕ} [NeZero n] (d : Fin n → Fin 4) :
    (∑ i : Fin n, (d (i + 1) - d i)) = 0 := by
  rw [Finset.sum_sub_distrib, sum_shift, sub_self]



theorem sum_turns_eq_smul {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    (∑ i : Fin n, (d (i + 1) - d i)) = cc d • (1 : Fin 4) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d (i + 1) - d i = 1)]
  have hP : ∑ i ∈ Finset.univ.filter (fun i => d (i + 1) - d i = 1), (d (i + 1) - d i)
      = cc d • (1 : Fin 4) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2), Finset.sum_const]
    rfl
  have hNP : ∑ i ∈ Finset.univ.filter (fun i => ¬ (d (i + 1) - d i = 1)), (d (i + 1) - d i) = 0
      := by
    apply Finset.sum_eq_zero
    intro i hi
    rcases hreflexfree i with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.1 hi).2
  rw [hP, hNP, add_zero]




theorem four_dvd_cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    4 ∣ cc d := by
  have hz : cc d • (1 : Fin 4) = 0 := by
    rw [← sum_turns_eq_smul d hreflexfree]; exact sum_turns_zero d
  have hz' : cc d • (1 : ZMod 4) = 0 := hz
  have hcast : ((cc d : ℕ) : ZMod 4) = 0 := by rw [nsmul_eq_mul, mul_one] at hz'; exact hz'
  exact (CharP.cast_eq_zero_iff (ZMod 4) 4 (cc d)).1 hcast




theorem stepOf_ne_zero (w : Fin 4) : stepOf w ≠ 0 := by
  fin_cases w <;> decide




theorem cc_pos {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    0 < cc d := by
  rcases Nat.eq_zero_or_pos (cc d) with h0 | h
  · exfalso
    have hempty : Finset.univ.filter (fun i : Fin n => d (i + 1) - d i = 1) = ∅ :=
      Finset.card_eq_zero.1 h0
    
    have hturn : ∀ i : Fin n, d (i + 1) = d i := by
      intro i
      rcases hreflexfree i with h | h
      · exact sub_eq_zero.1 h
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
          (by rw [hempty]; exact Finset.notMem_empty i)
    
    have haux : ∀ m : ℕ, d (Nat.cast m) = d 0 := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        have hcast : (Nat.cast (k + 1) : Fin n) = Nat.cast k + 1 := by
          apply Fin.ext
          rw [Fin.val_natCast, Fin.val_add, Fin.val_natCast, Fin.val_one',
            Nat.add_mod (k % n) (1 % n) n, Nat.mod_mod_of_dvd _ (dvd_refl n),
            Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod]
        rw [hcast, hturn (Nat.cast k), ih]
    have hconst : ∀ i : Fin n, d i = d 0 := by
      intro i
      have := haux i.val
      rwa [Fin.cast_val_eq_self] at this
    
    have hsum : ∑ i : Fin n, stepOf (d i) = n • stepOf (d 0) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [hconst i]), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
    rw [hsum] at hclosed
    have hz : (n : ℤ) • stepOf (d 0) = 0 := by
      rw [Nat.cast_smul_eq_nsmul]; exact hclosed
    rcases smul_eq_zero.1 hz with hn | hv
    · exact (NeZero.ne n) (by exact_mod_cast hn)
    · exact stepOf_ne_zero (d 0) hv
  · exact h


theorem four_le_cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    4 ≤ cc d :=
  Nat.le_of_dvd (cc_pos d hclosed hreflexfree) (four_dvd_cc d hreflexfree)
























theorem base_cc_eq_four {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hnodbl : Function.Injective (pos d) → cc d < 8) :
    cc d = 4 := by
  have hdvd := four_dvd_cc d hreflexfree
  have hge := four_le_cc d hclosed hreflexfree
  have hshort : cc d < 8 := hnodbl hsimple
  omega

end StatMech.Onsager.BaseCase
