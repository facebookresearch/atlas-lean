/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# The Piltz divisor functions

The Piltz divisor function `d_k(n)` counts the ordered factorisations `n = a₁ ⋯ a_k` into `k`
natural numbers, and `d_k^*(n)` counts those with every factor at least `2`. Both are expressed
through Mathlib's `Nat.finMulAntidiag`.

## Main definitions

* `ArithmeticFunction.piltz`: `d_k`
* `ArithmeticFunction.piltzNontrivial`: `d_k^*`

## Main statements

* `ArithmeticFunction.pow_apply_eq_sum_finMulAntidiag`:
  `(f ^ k) n = ∑_{a₁ ⋯ a_k = n} f a₁ ⋯ f a_k`
* `ArithmeticFunction.piltz_eq_zeta_pow`: `d_k = ζ ^ k`
* `ArithmeticFunction.piltz_two`: `d_2 = σ 0`
* `ArithmeticFunction.piltzNontrivial_eq_zeta_sub_one_pow`: `d_k^* = (ζ - 1) ^ k`
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace ArithmeticFunction

/-- The `k`-th Dirichlet power of an arithmetic function, evaluated at `n`, is the sum of
`∏ i, f (a i)` over the ordered `k`-tuples `a` of natural numbers with product `n`. -/
theorem pow_apply_eq_sum_finMulAntidiag {R : Type*} [CommSemiring R] (f : ArithmeticFunction R)
    (k n : ℕ) : (f ^ k) n = ∑ a ∈ Nat.finMulAntidiag k n, ∏ i, f (a i) := by
  induction k generalizing n with
  | zero =>
    rcases eq_or_ne n 1 with rfl | hn
    · simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left hn, one_apply_ne hn]
  | succ k ih =>
    rw [pow_succ', mul_apply]
    simp_rw [ih, mul_sum]
    rw [sum_sigma']
    refine sum_bij' (fun x _ => Fin.cons x.1.1 x.2)
      (fun a _ => ⟨(a 0, ∏ i, Fin.tail a i), Fin.tail a⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨d, e⟩, a⟩ h
      simp only [mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at h ⊢
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact ⟨by rw [h.2.1]; exact h.1.1, h.1.2⟩
    · intro a h
      simp only [mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at h ⊢
      rw [Fin.prod_univ_succ] at h
      refine ⟨⟨h.1, h.2⟩, ?_⟩
      simp only [Fin.tail, true_and, ne_eq]
      intro h0
      simp only [h0, mul_zero] at h
      exact h.2 h.1.symm
    · rintro ⟨⟨d, e⟩, a⟩ h
      simp only [mem_sigma, Nat.mem_finMulAntidiag] at h
      simp only [Fin.cons_zero, Fin.tail_cons, h.2.1]
    · intro a _
      simp
    · rintro ⟨⟨d, e⟩, a⟩ _
      rw [Fin.prod_univ_succ]
      simp

/-- The **Piltz divisor function** `d_k`: `piltz k n` is the number of ways of writing `n` as an
ordered product of `k` natural numbers. It is `0` at `n = 0`, `d_1 = ζ`, `d_2 = σ 0` and
`d_k = ζ ^ k` (`ArithmeticFunction.piltz_eq_zeta_pow`). -/
def piltz (k : ℕ) : ArithmeticFunction ℕ where
  toFun n := (Nat.finMulAntidiag k n).card
  map_zero' := by simp

/-- `piltz k n` counts the `k`-tuples in `Nat.finMulAntidiag k n`. -/
theorem piltz_apply (k n : ℕ) : piltz k n = (Nat.finMulAntidiag k n).card := rfl

/-- The Piltz divisor function `d_k` is the `k`-th Dirichlet power of `ζ`. -/
theorem piltz_eq_zeta_pow (k : ℕ) : piltz k = (ζ : ArithmeticFunction ℕ) ^ k := by
  ext n
  rw [piltz_apply, pow_apply_eq_sum_finMulAntidiag, card_eq_sum_ones]
  refine sum_congr rfl fun a ha => ?_
  rw [prod_eq_one]
  intro i _
  rw [zeta_apply_ne (Nat.ne_zero_of_mem_finMulAntidiag ha i)]

/-- `d_0` is the identity `1` for Dirichlet convolution. -/
@[simp] theorem piltz_zero : piltz 0 = 1 := by simp [piltz_eq_zeta_pow]

/-- `d_1 = ζ`. -/
@[simp] theorem piltz_one : piltz 1 = ζ := by simp [piltz_eq_zeta_pow]

/-- `d_{k+1} = d_k * ζ`. -/
theorem piltz_succ (k : ℕ) : piltz (k + 1) = piltz k * ζ := by
  simp [piltz_eq_zeta_pow, pow_succ]

/-- `d_{k+1}(n) = ∑_{d ∣ n} d_k(d)`. -/
theorem piltz_succ_apply (k n : ℕ) : piltz (k + 1) n = ∑ d ∈ n.divisors, piltz k d := by
  rw [piltz_succ, mul_zeta_apply]

/-- `d_2` is the number-of-divisors function `σ 0`. -/
@[simp] theorem piltz_two : piltz 2 = σ 0 := by
  ext n
  rw [piltz_succ_apply, sigma_zero_apply, card_eq_sum_ones]
  refine sum_congr rfl fun d hd => ?_
  simp [Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]

/-- `d_k(n) ≤ d_{k+1}(n)` for `n ≠ 0`. -/
theorem piltz_le_piltz_succ (k : ℕ) {n : ℕ} (hn : n ≠ 0) : piltz k n ≤ piltz (k + 1) n := by
  rw [piltz_succ_apply]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn)

/-- `d_k(n)` is positive for `k ≠ 0` and `n ≠ 0`. -/
theorem piltz_pos {k n : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) : 0 < piltz k n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  induction k with
  | zero => simp [hn]
  | succ k ih => exact (ih k.succ_ne_zero).trans_le (piltz_le_piltz_succ _ hn)

/-- The **nontrivial Piltz divisor function** `d_k^*`: `piltzNontrivial k n` is the number of
ways of writing `n` as an ordered product of `k` natural numbers that are all at least `2`.
Over `ℤ` it is `(ζ - 1) ^ k` (`ArithmeticFunction.piltzNontrivial_eq_zeta_sub_one_pow`). -/
def piltzNontrivial (k : ℕ) : ArithmeticFunction ℕ where
  toFun n := {a ∈ Nat.finMulAntidiag k n | ∀ i, 1 < a i}.card
  map_zero' := by simp

/-- `piltzNontrivial k n` counts the `k`-tuples in `Nat.finMulAntidiag k n` with all entries
greater than `1`. -/
theorem piltzNontrivial_apply (k n : ℕ) :
    piltzNontrivial k n = {a ∈ Nat.finMulAntidiag k n | ∀ i, 1 < a i}.card := rfl

/-- `d_k^* = (ζ - 1) ^ k` as integer-valued arithmetic functions. -/
theorem piltzNontrivial_eq_zeta_sub_one_pow (k : ℕ) :
    (piltzNontrivial k : ArithmeticFunction ℤ) = ((ζ : ArithmeticFunction ℤ) - 1) ^ k := by
  ext n
  rw [natCoe_apply, piltzNontrivial_apply, pow_apply_eq_sum_finMulAntidiag, card_filter]
  push_cast
  refine sum_congr rfl fun a ha => ?_
  have h0 := Nat.ne_zero_of_mem_finMulAntidiag ha
  have hterm : ∀ i, ((ζ : ArithmeticFunction ℤ) - 1) (a i) = if 1 < a i then 1 else 0 := by
    intro i
    rw [sub_eq_add_neg, add_apply, neg_apply, natCoe_apply, zeta_apply_ne (h0 i)]
    rcases eq_or_ne (a i) 1 with h | h
    · simp [h]
    · simp [one_apply_ne h, show 1 < a i by have := h0 i; omega]
  simp_rw [hterm, prod_ite_zero, prod_const_one]
  simp

end ArithmeticFunction
