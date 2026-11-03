/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Closed lattice walks given by direction sequences

A cyclic sequence of unit steps on `ℤ²` is encoded by its directions `d : Fin n → Fin 4`, where
`0, 1, 2, 3` stand for east, north, west, south. The walk visits the vertices `pos d k`, the
partial sums of the steps; it is closed when the steps sum to zero and simple when `pos d` is
injective. The turn at step `i` is `d (i + 1) - d i ∈ Fin 4`; `cc d` counts the counterclockwise
(left) turns, those with `d (i + 1) - d i = 1`.

This file treats walks without right turns or reversals, i.e. every turn is `0` (straight) or `1`
(left). For such a walk the left turns add up to a multiple of a full revolution, so `4 ∣ cc d`,
and a closed walk turns at least once, so `4 ≤ cc d`.

## Main definitions

* `StatMech.Onsager.BaseCase.stepOf`: the unit step in direction `w : Fin 4`.
* `StatMech.Onsager.BaseCase.pos`: the `k`-th vertex of the walk, starting at the origin.
* `StatMech.Onsager.BaseCase.cc`: the number of left turns.

## Main results

* `StatMech.Onsager.BaseCase.four_dvd_cc`, `StatMech.Onsager.BaseCase.four_le_cc`: a closed walk
  with only straight steps and left turns has a positive multiple of `4` left turns.
* `StatMech.Onsager.BaseCase.base_cc_eq_four`: such a walk has exactly four left turns provided
  it has fewer than eight; the unconditional statement is
  `StatMech.Onsager.UmlaufsatzFinal.cc_eq_four_of_no_right_turn`.
-/

@[expose] public section

namespace StatMech.Onsager.BaseCase

open Finset
open Fin.NatCast

/-- The unit step of `ℤ²` in direction `w`: `0 ↦ (1, 0)` (east), `1 ↦ (0, 1)` (north), `2 ↦ (-1, 0)`
  (west), `3 ↦ (0, -1)` (south). -/
def stepOf : Fin 4 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

/-- The `k`-th vertex of the lattice walk with step directions `d`: the sum of the steps `stepOf (d
  i)` for `i < k`, so that `pos d 0 = 0`. -/
def pos {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (k : Fin n) : ℤ × ℤ :=
  ∑ i ∈ Finset.filter (· < k) Finset.univ, stepOf (d i)

/-- The number of counterclockwise (left) quarter turns of the cyclic direction sequence `d`, i.e.
  of indices `i` with `d (i + 1) - d i = 1`. -/
def cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d (i + 1) - d i = 1)).card

/-- The turns of a cyclic direction sequence sum to zero in `Fin 4`. -/
theorem sum_turns_zero {n : ℕ} [NeZero n] (d : Fin n → Fin 4) :
    (∑ i : Fin n, (d (i + 1) - d i)) = 0 := by
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (Equiv.sum_comp (Equiv.addRight (1 : Fin n)) d)

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

/-- If every turn is straight or left, the number of left turns is divisible by `4`. -/
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

/-- A closed walk with only straight steps and left turns turns at least once. -/
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

/-- A closed walk with only straight steps and left turns has at least four left turns. -/
theorem four_le_cc {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    4 ≤ cc d :=
  Nat.le_of_dvd (cc_pos d hclosed hreflexfree) (four_dvd_cc d hreflexfree)

/-- A closed walk with only straight steps and left turns has exactly four left turns, provided
  simplicity rules out eight or more. -/
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
