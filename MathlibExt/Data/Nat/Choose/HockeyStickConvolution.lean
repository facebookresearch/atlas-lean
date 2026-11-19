/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Provenance: the proof of `Nat.sum_antidiagonal_choose_mul_choose` is relocated from the private
`choose_convolution` that Adam Kiezun added to
`MathlibExt/Combinatorics/Enumerative/MotzkinNumber.lean` in `facebookresearch/atlas-lean`
PR #876 (commit `0d013ae96479440feda771bf937aa95bb39e41cd`), as of immutable atlas-lean commit
`18d1aa399b6ebaa8cd9c4a48795b43f6734c3785`. The induction, the `p = 0` antidiagonal swap and the
Pascal step are unchanged apart from name qualification; the `q = 0` hockey-stick step uses
Mathlib's `Nat.sum_Icc_choose` (through the private range wrapper below) instead of the source's
private `choose_sum`. The range wrapper and the `range` form `Nat.sum_range_choose_mul_choose_sub`
are local additions. The Meta Platforms notice above is that source file's header, preserved
verbatim.
-/

module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The hockey-stick convolution

The upper-index Chu–Vandermonde identity
`∑_{a + b = n} C(a, p) C(b, q) = C(n + 1, p + q + 1)`, stated over the antidiagonal
(`Nat.sum_antidiagonal_choose_mul_choose`) and over `range`
(`Nat.sum_range_choose_mul_choose_sub`). The case `q = 0` is Mathlib's hockey-stick identity
`Nat.sum_Icc_choose`, from which the proof starts.

`MathlibExt.Combinatorics.Enumerative.ShiftedEulerianHankel` and
`MathlibExt.Combinatorics.Enumerative.MotzkinNumber` both use these statements.
-/

@[expose] public section

open Finset

namespace Nat

/-- Mathlib's hockey-stick identity `Nat.sum_Icc_choose`, summed over `range (n + 1)`. -/
private theorem sum_range_choose_eq_choose_add_one (n k : ℕ) :
    ∑ i ∈ range (n + 1), i.choose k = (n + 1).choose (k + 1) := by
  rw [← sum_Icc_choose n k]
  refine (sum_subset (fun i hi => ?_) fun i hi hik => ?_).symm
  · simp only [mem_Icc, mem_range] at hi ⊢
    omega
  · simp only [mem_Icc, mem_range, not_and, not_le] at hi hik
    exact choose_eq_zero_of_lt (Nat.lt_of_not_le fun h => absurd (hik h) (by omega))

/-- **Hockey-stick convolution** (upper-index Chu–Vandermonde identity):
`∑_{a + b = n} C(a, p) C(b, q) = C(n + 1, p + q + 1)`. -/
theorem sum_antidiagonal_choose_mul_choose (n p q : ℕ) :
    ∑ ab ∈ antidiagonal n, ab.1.choose p * ab.2.choose q = (n + 1).choose (p + q + 1) := by
  induction n generalizing p q with
  | zero =>
    cases p <;> cases q <;> simp [choose_succ_succ, choose_zero_succ, ← Nat.add_assoc]
  | succ n ih =>
    cases p with
    | zero =>
      simp only [choose_zero_right, one_mul, zero_add]
      rw [← Finset.Nat.sum_antidiagonal_swap]
      simp only [Prod.snd_swap]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => a.choose q)]
      exact sum_range_choose_eq_choose_add_one (n + 1) q
    | succ p =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [choose_zero_succ, zero_mul, zero_add]
      conv_lhs => simp only [choose_succ_succ, add_mul]
      rw [sum_add_distrib, ih, ih]
      simpa only [succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (choose_succ_succ (n + 1) (p + q + 1)).symm

/-- `range` form of `Nat.sum_antidiagonal_choose_mul_choose`:
`∑_{i ≤ n} C(i, p) C(n - i, q) = C(n + 1, p + q + 1)`. -/
theorem sum_range_choose_mul_choose_sub (n p q : ℕ) :
    ∑ i ∈ range (n + 1), i.choose p * (n - i).choose q = (n + 1).choose (p + q + 1) := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => i.choose p * j.choose q)]
  exact sum_antidiagonal_choose_mul_choose n p q

end Nat
