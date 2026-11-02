/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Binomial transform of Pell numbers via Kronecker symbol
-/

/-- Binet formula for the Pell sequence, over `ℂ`. -/
private theorem pell_complex_binet (P : ℕ → ℤ) (h0 : P 0 = 0) (h1 : P 1 = 1)
    (hrec : ∀ n, P (n + 2) = 2 * P (n + 1) + P n) (s : ℂ) (hs2 : s ^ 2 = 2)
    (i : ℕ) : (P i : ℂ) = ((1 + s) ^ i - (1 - s) ^ i) / (2 * s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs2
    norm_num at hs2
  refine Nat.twoStepInduction ?_ ?_ (fun n ih1 ih2 => ?_) i
  · rw [h0]
    simp
  · rw [h1]
    simp only [Int.cast_one, pow_one]
    rw [show (1 + s) - (1 - s) = 2 * s by ring,
      div_self (mul_ne_zero two_ne_zero hs0)]
  · have ha : (1 + s) ^ (n + 2) = 2 * (1 + s) ^ (n + 1) + (1 + s) ^ n := by
      have h2 : (1 + s) ^ 2 = 2 * (1 + s) + 1 := by linear_combination hs2
      calc (1 + s) ^ (n + 2) = (1 + s) ^ n * (1 + s) ^ 2 := by ring
        _ = (1 + s) ^ n * (2 * (1 + s) + 1) := by rw [h2]
        _ = 2 * (1 + s) ^ (n + 1) + (1 + s) ^ n := by ring
    have hb : (1 - s) ^ (n + 2) = 2 * (1 - s) ^ (n + 1) + (1 - s) ^ n := by
      have h2 : (1 - s) ^ 2 = 2 * (1 - s) + 1 := by linear_combination hs2
      calc (1 - s) ^ (n + 2) = (1 - s) ^ n * (1 - s) ^ 2 := by ring
        _ = (1 - s) ^ n * (2 * (1 - s) + 1) := by rw [h2]
        _ = 2 * (1 - s) ^ (n + 1) + (1 - s) ^ n := by ring
    have hrecC : ((P (n + 2) : ℤ) : ℂ)
        = 2 * ((P (n + 1) : ℤ) : ℂ) + ((P n : ℤ) : ℂ) := by
      exact_mod_cast hrec n
    rw [hrecC, ih1, ih2, ← mul_div_assoc, ← add_div]
    congr 1
    linear_combination -ha + hb

/-- Binomial theorem in summation form. -/
private theorem binom_sum_pow (z : ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * z ^ i = (1 + z) ^ n := by
  have h := add_pow z (1 : ℂ) n
  rw [add_comm z 1] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Closed form for the binomial transform of the Pell sequence. -/
private theorem pell_binom_closed (P : ℕ → ℤ) (h0 : P 0 = 0) (h1 : P 1 = 1)
    (hrec : ∀ n, P (n + 2) = 2 * P (n + 1) + P n) (s : ℂ) (hs2 : s ^ 2 = 2)
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (P i : ℂ) =
      ((2 + s) ^ n - (2 - s) ^ n) / (2 * s) := by
  have hbin := pell_complex_binet P h0 h1 hrec s hs2
  have e : ∀ i : ℕ, (n.choose i : ℂ) * (P i : ℂ) =
      (((n.choose i : ℂ) * (1 + s) ^ i - (n.choose i : ℂ) * (1 - s) ^ i)
        / (2 * s)) := by
    intro i
    rw [hbin i]
    ring
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, binom_sum_pow, binom_sum_pow]
  congr 1
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- Powers of `w` repeat with period 8. -/
private theorem omega_pow_mod (w : ℂ) (hw8 : w ^ 8 = 1) (k : ℕ) : w ^ k = w ^ (k % 8) := by
  conv_lhs => rw [← Nat.div_add_mod k 8]
  rw [pow_add, pow_mul, hw8, one_pow, one_mul]

/-- Powers of `w ^ 3` repeat with period 8. -/
private theorem omega_pow3_mod (w : ℂ) (hw8 : w ^ 8 = 1) (k : ℕ) :
    w ^ (3 * k) = w ^ ((3 * k) % 8) := by
  have e : 3 * k = 8 * (3 * (k / 8)) + 3 * (k % 8) := by
    have h := Nat.div_add_mod k 8
    omega
  have e2 : (3 * (k % 8)) % 8 = (3 * k) % 8 := by
    have h := Nat.div_add_mod k 8
    omega
  conv_lhs => rw [e, pow_add, pow_mul, hw8, one_pow, one_mul]
  rw [← e2]
  exact omega_pow_mod w hw8 (3 * (k % 8))

/-- Roots-of-unity filter for the Kronecker symbol `(k/8)`. -/
private theorem kron_filter (s w : ℂ) (hs2 : s ^ 2 = 2) (hs0 : s ≠ 0)
    (hw : w = (1 + Complex.I) / s) (k : ℕ) :
    2 * s * (if k % 2 = 0 then (0 : ℂ)
      else if k % 8 = 1 ∨ k % 8 = 7 then (1 : ℂ) else (-1 : ℂ)) =
    w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹ := by
  have h1I : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((1 : ℂ) + Complex.I).im = ((0 : ℂ)).im := congrArg Complex.im h
    rw [Complex.add_im, Complex.one_im, Complex.I_im, Complex.zero_im] at him
    norm_num at him
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero h1I hs0
  have hI2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    linear_combination Complex.I_mul_I
  have hIsq : Complex.I ^ 2 = -1 := by
    linear_combination Complex.I_mul_I
  have hsw : s * w = 1 + Complex.I := by
    rw [hw, mul_comm s _, div_mul_cancel₀ _ hs0]
  have hw2 : w ^ 2 = Complex.I := by
    rw [hw, div_pow, hI2, hs2]
    exact mul_div_cancel_left₀ _ two_ne_zero
  have hw4 : w ^ 4 = -1 := by
    calc w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = -1 := by rw [hw2, hIsq]
  have hw8 : w ^ 8 = 1 := by
    calc w ^ 8 = (w ^ 4) ^ 2 := by ring
      _ = 1 := by rw [hw4]; norm_num
  have hw5 : w ^ 5 = -w := by
    calc w ^ 5 = w ^ 4 * w := by ring
      _ = -w := by rw [hw4]; ring
  have hw6 : w ^ 6 = -Complex.I := by
    calc w ^ 6 = w ^ 4 * w ^ 2 := by ring
      _ = -Complex.I := by rw [hw4, hw2]; ring
  have hw7 : w ^ 7 = -(w ^ 3) := by
    calc w ^ 7 = w ^ 4 * w ^ 3 := by ring
      _ = -(w ^ 3) := by rw [hw4]; ring
  have hswinv : s * w⁻¹ = 1 - Complex.I := by
    have hwinv : w⁻¹ = s / (1 + Complex.I) := by rw [hw, inv_div]
    rw [hwinv, ← mul_div_assoc, ← pow_two, hs2, div_eq_iff h1I]
    linear_combination Complex.I_mul_I
  have hws : w + w⁻¹ = s := by
    have h : s * (w + w⁻¹) = s * s := by
      rw [mul_add, hsw, hswinv]
      linear_combination -hs2
    exact mul_left_cancel₀ hs0 h
  have hws3 : w ^ 3 + (w ^ 3)⁻¹ = -s := by
    have hsw3 : s * w ^ 3 = Complex.I - 1 := by
      have e : s * w ^ 3 = (s * w) * w ^ 2 := by ring
      rw [e, hsw, hw2]
      linear_combination Complex.I_mul_I
    have hswinv3 : s * (w ^ 3)⁻¹ = -1 - Complex.I := by
      have e : s * (w ^ 3)⁻¹ = (s * w⁻¹) * (w⁻¹) ^ 2 := by
        rw [← inv_pow]
        ring
      rw [e, hswinv]
      have hwinv2 : (w⁻¹) ^ 2 = -Complex.I := by
        rw [inv_pow, hw2, Complex.inv_I]
      rw [hwinv2]
      linear_combination Complex.I_mul_I
    have h : s * (w ^ 3 + (w ^ 3)⁻¹) = s * (-s) := by
      rw [mul_add, hsw3, hswinv3]
      linear_combination hs2
    exact mul_left_cancel₀ hs0 h
  rw [omega_pow_mod w hw8 k, omega_pow3_mod w hw8 k]
  have h8 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨
      k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h
  · have hk2 : k % 2 = 0 := by omega
    have h3 : (3 * k) % 8 = 0 := by omega
    rw [h, hk2, h3, ite_eq_left rfl, pow_zero, inv_one]
    ring
  · have hk2 : k % 2 = 1 := by omega
    have h3 : (3 * k) % 8 = 3 := by omega
    rw [h, hk2, h3, ite_eq_right one_ne_zero, ite_eq_left (Or.inl rfl), pow_one]
    linear_combination -hws + hws3
  · have hk2 : k % 2 = 0 := by omega
    have h3 : (3 * k) % 8 = 6 := by omega
    rw [h, hk2, h3, ite_eq_left rfl, hw2, hw6, inv_neg, Complex.inv_I, neg_neg]
    ring
  · have hk2 : k % 2 = 1 := by omega
    have h3 : (3 * k) % 8 = 1 := by omega
    rw [h, hk2, h3, ite_eq_right one_ne_zero, ite_eq_right (by decide), pow_one]
    linear_combination hws - hws3
  · have hk2 : k % 2 = 0 := by omega
    have h3 : (3 * k) % 8 = 4 := by omega
    rw [h, hk2, h3, ite_eq_left rfl, hw4, inv_neg, inv_one]
    ring
  · have hk2 : k % 2 = 1 := by omega
    have h3 : (3 * k) % 8 = 7 := by omega
    rw [h, hk2, h3, ite_eq_right one_ne_zero, ite_eq_right (by decide), hw5, hw7,
      inv_neg, inv_neg]
    linear_combination hws - hws3
  · have hk2 : k % 2 = 0 := by omega
    have h3 : (3 * k) % 8 = 2 := by omega
    rw [h, hk2, h3, ite_eq_left rfl, hw6, hw2, inv_neg, Complex.inv_I, neg_neg]
    ring
  · have hk2 : k % 2 = 1 := by omega
    have h3 : (3 * k) % 8 = 5 := by omega
    rw [h, hk2, h3, ite_eq_right one_ne_zero, ite_eq_left (Or.inr rfl), hw7, hw5,
      inv_neg, inv_neg]
    linear_combination -hws + hws3

/-- Symmetrization: twice the half-sum equals the full symmetric sum. -/
private theorem kron_symm (w : ℂ) (hw0 : w ≠ 0) (n : ℕ) :
    2 * (∑ k ∈ Finset.range (n + 1),
      (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
      ((2 * n).choose (n + k) : ℂ)) =
    ∑ m ∈ Finset.range (2 * n + 1),
      (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
        ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) := by
  have hpsd : ∀ a b : ℕ, b ≤ a → w ^ (a - b) = w ^ a * (w ^ b)⁻¹ := by
    intro a b hab
    have h1 : w ^ (a - b) * w ^ b = w ^ a := by
      rw [← pow_add, Nat.sub_add_cancel hab]
    have h2 : w ^ b ≠ 0 := pow_ne_zero b hw0
    rw [← div_eq_mul_inv, eq_div_iff h2]
    exact h1
  have hC : ∀ j : ℕ, j ≤ n →
      (2 * n).choose (n + (n - j)) = (2 * n).choose j := by
    intro j hjn
    have e1 : n + (n - j) = 2 * n - j := by omega
    rw [e1]
    exact Nat.choose_symm (by omega)
  have hFlower : ∀ j : ℕ, j ≤ n →
      w ^ (n - j) + (w ^ (n - j))⁻¹ - w ^ (3 * (n - j)) -
        (w ^ (3 * (n - j)))⁻¹ =
      w ^ n * (w ^ j)⁻¹ + (w ^ n)⁻¹ * w ^ j - (w ^ 3) ^ n * ((w ^ 3) ^ j)⁻¹ -
        ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ j := by
    intro j hjn
    have e1 := hpsd n j hjn
    have e3 : w ^ (3 * (n - j)) = (w ^ 3) ^ n * ((w ^ 3) ^ j)⁻¹ := by
      have e : 3 * (n - j) = 3 * n - 3 * j := by omega
      rw [e]
      have e2 := hpsd (3 * n) (3 * j) (by omega)
      rw [e2, pow_mul, pow_mul]
    rw [e1, e3, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
      mul_comm (w ^ j) _, mul_comm ((w ^ 3) ^ j) _]
  have hFupper : ∀ m : ℕ, n ≤ m → m ≤ 2 * n →
      w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
        (w ^ (3 * (m - n)))⁻¹ =
      w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
        ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m := by
    intro m hnm hmn
    have u1 := hpsd m n hnm
    have u3 : w ^ (3 * (m - n)) = (w ^ 3) ^ m * ((w ^ 3) ^ n)⁻¹ := by
      have e : 3 * (m - n) = 3 * m - 3 * n := by omega
      rw [e]
      have e2 := hpsd (3 * m) (3 * n) (by omega)
      rw [e2, pow_mul, pow_mul]
    rw [u1, u3, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
      mul_comm (w ^ m) _, mul_comm ((w ^ 3) ^ m) _]
    abel
  have hrefl : (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) =
      ∑ j ∈ Finset.range (n + 1),
        (w ^ n * (w ^ j)⁻¹ + (w ^ n)⁻¹ * w ^ j - (w ^ 3) ^ n * ((w ^ 3) ^ j)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ j) * ((2 * n).choose j : ℂ) := by
    have hr := Finset.sum_range_reflect
      (fun k => (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) (n + 1)
    have hr' : (∑ j ∈ Finset.range (n + 1),
          (w ^ (n + 1 - 1 - j) + (w ^ (n + 1 - 1 - j))⁻¹ -
            w ^ (3 * (n + 1 - 1 - j)) - (w ^ (3 * (n + 1 - 1 - j)))⁻¹) *
          ((2 * n).choose (n + (n + 1 - 1 - j)) : ℂ)) =
        (∑ j ∈ Finset.range (n + 1),
          (w ^ j + (w ^ j)⁻¹ - w ^ (3 * j) - (w ^ (3 * j))⁻¹) *
          ((2 * n).choose (n + j) : ℂ)) := hr
    rw [← hr']
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by
      have hlt := Finset.mem_range.mp hj
      omega
    have e : n + 1 - 1 - j = n - j := by omega
    rw [e, hC j hjn, hFlower j hjn]
  have hVico : (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) =
      ∑ m ∈ Finset.Ico n (2 * n + 1),
        (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
          (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ) := by
    have h := Finset.sum_Ico_eq_sum_range
      (fun m => (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
        (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) n (2 * n + 1)
    have h' : (∑ m ∈ Finset.Ico n (2 * n + 1),
          (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
            (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) =
        (∑ k ∈ Finset.range (2 * n + 1 - n),
          (w ^ (n + k - n) + (w ^ (n + k - n))⁻¹ - w ^ (3 * (n + k - n)) -
            (w ^ (3 * (n + k - n)))⁻¹) * ((2 * n).choose (n + k) : ℂ)) := h
    have e1 : 2 * n + 1 - n = n + 1 := by omega
    rw [e1] at h'
    rw [h']
    apply Finset.sum_congr rfl
    intro k _
    have e2 : n + k - n = k := by omega
    rw [e2]
  have hVsplit : (∑ m ∈ Finset.Ico n (2 * n + 1),
        (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
          (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) =
      (w ^ 0 + (w ^ 0)⁻¹ - w ^ (3 * 0) - (w ^ (3 * 0))⁻¹) *
        ((2 * n).choose n : ℂ) +
      ∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
        (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
          (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ) := by
    have hcon := Finset.sum_Ico_consecutive
      (fun m => (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
        (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ))
      (Nat.le_succ n) (show n + 1 ≤ 2 * n + 1 by omega)
    have hcon' : (∑ m ∈ Finset.Ico n (n + 1),
          (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
            (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) +
        (∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
          (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
            (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) =
        ∑ m ∈ Finset.Ico n (2 * n + 1),
          (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
            (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ) := hcon
    rw [← hcon']
    have hsing : Finset.Ico n (n + 1) = {n} := by
      ext m
      rw [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hsing, Finset.sum_singleton]
    have e0 : n - n = 0 := by omega
    rw [e0]
  have hFsplit : (∑ m ∈ Finset.range (2 * n + 1),
        (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ)) =
      (∑ m ∈ Finset.range (n + 1),
        (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ)) +
      ∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
        (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) := by
    have hcon := Finset.sum_Ico_consecutive
      (fun m => (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n *
        ((w ^ 3) ^ m)⁻¹ - ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) *
        ((2 * n).choose m : ℂ))
      (Nat.zero_le (n + 1)) (show n + 1 ≤ 2 * n + 1 by omega)
    have hcon' : (∑ m ∈ Finset.Ico 0 (n + 1),
          (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n *
            ((w ^ 3) ^ m)⁻¹ - ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) *
          ((2 * n).choose m : ℂ)) +
        (∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
          (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n *
            ((w ^ 3) ^ m)⁻¹ - ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) *
          ((2 * n).choose m : ℂ)) =
        ∑ m ∈ Finset.Ico 0 (2 * n + 1),
          (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n *
            ((w ^ 3) ^ m)⁻¹ - ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) *
          ((2 * n).choose m : ℂ) := hcon
    simp only [← Finset.range_eq_Ico] at hcon'
    exact hcon'.symm
  have hUpper : (∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
        (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
          (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ)) =
      ∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
        (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmem := Finset.mem_Ico.mp hm
    have hnm : n ≤ m := by omega
    have hmn : m ≤ 2 * n := by omega
    rw [hFupper m hnm hmn]
  have hF0 : (w ^ 0 + (w ^ 0)⁻¹ - w ^ (3 * 0) - (w ^ (3 * 0))⁻¹) *
      ((2 * n).choose n : ℂ) = 0 := by
    rw [mul_zero, pow_zero, inv_one]
    ring
  have e1 : (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) =
      (w ^ 0 + (w ^ 0)⁻¹ - w ^ (3 * 0) - (w ^ (3 * 0))⁻¹) *
        ((2 * n).choose n : ℂ) +
      ∑ m ∈ Finset.Ico (n + 1) (2 * n + 1),
        (w ^ (m - n) + (w ^ (m - n))⁻¹ - w ^ (3 * (m - n)) -
          (w ^ (3 * (m - n)))⁻¹) * ((2 * n).choose m : ℂ) :=
    hVico.trans hVsplit
  have e2 : (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) =
      ∑ m ∈ Finset.range (n + 1),
        (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
          ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) := hrefl
  linear_combination e1 + e2 + hUpper - hFsplit + hF0

/-- Evaluation of the full symmetric sum by the binomial theorem. -/
private theorem kron_geom (s w : ℂ) (hs2 : s ^ 2 = 2) (hs0 : s ≠ 0)
    (hw : w = (1 + Complex.I) / s) (n : ℕ) :
    (∑ m ∈ Finset.range (2 * n + 1),
      (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
        ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ)) =
    2 * ((2 + s) ^ n - (2 - s) ^ n) := by
  have h1I : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((1 : ℂ) + Complex.I).im = ((0 : ℂ)).im := congrArg Complex.im h
    rw [Complex.add_im, Complex.one_im, Complex.I_im, Complex.zero_im] at him
    norm_num at him
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero h1I hs0
  have hsw : s * w = 1 + Complex.I := by
    rw [hw, mul_comm s _, div_mul_cancel₀ _ hs0]
  have hw2 : w ^ 2 = Complex.I := by
    have hI2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
      linear_combination Complex.I_mul_I
    rw [hw, div_pow, hI2, hs2]
    exact mul_div_cancel_left₀ _ two_ne_zero
  have hswinv : s * w⁻¹ = 1 - Complex.I := by
    have hwinv : w⁻¹ = s / (1 + Complex.I) := by rw [hw, inv_div]
    have h2 : (2 : ℂ) / (1 + Complex.I) = 1 - Complex.I := by
      rw [div_eq_iff h1I]
      linear_combination Complex.I_mul_I
    calc s * w⁻¹ = s ^ 2 / (1 + Complex.I) := by rw [hwinv, ← mul_div_assoc, ← pow_two]
      _ = 2 / (1 + Complex.I) := by rw [hs2]
      _ = 1 - Complex.I := h2
  have hwinv2 : (w⁻¹) ^ 2 = -Complex.I := by
    rw [inv_pow, hw2, Complex.inv_I]
  have hSq1 : (1 + w) ^ 2 = (2 + s) * w := by
    have e : (1 + w) ^ 2 = 1 + 2 * w + w ^ 2 := by ring
    have e2 : (2 + s) * w = 2 * w + (1 + Complex.I) := by
      rw [add_mul, hsw]
    rw [e, hw2, e2]
    ring
  have hSq1i : (1 + w⁻¹) ^ 2 = (2 + s) * w⁻¹ := by
    have e : (1 + w⁻¹) ^ 2 = 1 + 2 * w⁻¹ + (w⁻¹) ^ 2 := by ring
    have e2 : (2 + s) * w⁻¹ = 2 * w⁻¹ + (1 - Complex.I) := by
      rw [add_mul, hswinv]
    rw [e, hwinv2, e2]
    ring
  have hw6 : w ^ 6 = -Complex.I := by
    have hw4 : w ^ 4 = -1 := by
      have hIsq : Complex.I ^ 2 = -1 := by
        linear_combination Complex.I_mul_I
      calc w ^ 4 = (w ^ 2) ^ 2 := by ring
        _ = -1 := by rw [hw2, hIsq]
    calc w ^ 6 = w ^ 4 * w ^ 2 := by ring
      _ = -Complex.I := by rw [hw4, hw2]; ring
  have hw32 : (w ^ 3) ^ 2 = -Complex.I := by
    rw [← pow_mul]
    exact hw6
  have hswinv3 : s * (w ^ 3)⁻¹ = -1 - Complex.I := by
    have e : s * (w ^ 3)⁻¹ = (s * w⁻¹) * (w⁻¹) ^ 2 := by
      rw [← inv_pow]
      ring
    rw [e, hswinv, hwinv2]
    linear_combination Complex.I_mul_I
  have hu2 : ((w ^ 3)⁻¹) ^ 2 = Complex.I := by
    rw [inv_pow, hw32, inv_neg, Complex.inv_I, neg_neg]
  have hSq3 : (1 + w ^ 3) ^ 2 = (2 - s) * w ^ 3 := by
    have e : (1 + w ^ 3) ^ 2 = 1 + 2 * w ^ 3 + (w ^ 3) ^ 2 := by ring
    have e2 : (2 - s) * w ^ 3 = 2 * w ^ 3 - (Complex.I - 1) := by
      have hsw3 : s * w ^ 3 = Complex.I - 1 := by
        have ee : s * w ^ 3 = (s * w) * w ^ 2 := by ring
        rw [ee, hsw, hw2]
        linear_combination Complex.I_mul_I
      rw [sub_mul, hsw3]
    rw [e, hw32, e2]
    ring
  have hSq3i : (1 + (w ^ 3)⁻¹) ^ 2 = (2 - s) * (w ^ 3)⁻¹ := by
    have e : (1 + (w ^ 3)⁻¹) ^ 2
        = 1 + 2 * (w ^ 3)⁻¹ + ((w ^ 3)⁻¹) ^ 2 := by ring
    have e2 : (2 - s) * (w ^ 3)⁻¹ = 2 * (w ^ 3)⁻¹ - (-1 - Complex.I) := by
      rw [sub_mul, hswinv3]
    rw [e, hu2, e2]
    ring
  have gS2 : (∑ m ∈ Finset.range (2 * n + 1),
        ((w ^ n)⁻¹ * w ^ m) * ((2 * n).choose m : ℂ)) = (2 + s) ^ n := by
    have e : ∀ m : ℕ, ((w ^ n)⁻¹ * w ^ m) * ((2 * n).choose m : ℂ) =
        (w ^ n)⁻¹ * (((2 * n).choose m : ℂ) * w ^ m) := fun m => by ring
    simp only [e]
    rw [← Finset.mul_sum, binom_sum_pow, pow_mul, hSq1, mul_pow,
      ← mul_assoc, mul_comm ((w ^ n)⁻¹) _, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n hw0), mul_one]
  have gS1 : (∑ m ∈ Finset.range (2 * n + 1),
        (w ^ n * (w ^ m)⁻¹) * ((2 * n).choose m : ℂ)) = (2 + s) ^ n := by
    have e : ∀ m : ℕ, (w ^ n * (w ^ m)⁻¹) * ((2 * n).choose m : ℂ) =
        w ^ n * (((2 * n).choose m : ℂ) * (w⁻¹) ^ m) := by
      intro m
      rw [← inv_pow]
      ring
    simp only [e]
    rw [← Finset.mul_sum, binom_sum_pow, pow_mul, hSq1i, mul_pow,
      ← mul_assoc, mul_comm (w ^ n) _, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hw0, one_pow, mul_one]
  have gS4 : (∑ m ∈ Finset.range (2 * n + 1),
        (((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ)) =
      (2 - s) ^ n := by
    have e : ∀ m : ℕ, (((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) =
        ((w ^ 3) ^ n)⁻¹ * (((2 * n).choose m : ℂ) * (w ^ 3) ^ m) := fun m => by ring
    simp only [e]
    rw [← Finset.mul_sum, binom_sum_pow, pow_mul, hSq3, mul_pow,
      ← mul_assoc, mul_comm (((w ^ 3) ^ n)⁻¹) _, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n (pow_ne_zero 3 hw0)), mul_one]
  have gS3 : (∑ m ∈ Finset.range (2 * n + 1),
        ((w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹) * ((2 * n).choose m : ℂ)) =
      (2 - s) ^ n := by
    have e : ∀ m : ℕ, ((w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹) * ((2 * n).choose m : ℂ) =
        (w ^ 3) ^ n * (((2 * n).choose m : ℂ) * ((w ^ 3)⁻¹) ^ m) := by
      intro m
      rw [← inv_pow]
      ring
    simp only [e]
    rw [← Finset.mul_sum, binom_sum_pow, pow_mul, hSq3i, mul_pow,
      ← mul_assoc, mul_comm ((w ^ 3) ^ n) _, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (pow_ne_zero 3 hw0), one_pow, mul_one]
  have hsplit : ∀ m : ℕ,
      (w ^ n * (w ^ m)⁻¹ + (w ^ n)⁻¹ * w ^ m - (w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹ -
        ((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) =
      (w ^ n * (w ^ m)⁻¹) * ((2 * n).choose m : ℂ) +
        ((w ^ n)⁻¹ * w ^ m) * ((2 * n).choose m : ℂ) -
        ((w ^ 3) ^ n * ((w ^ 3) ^ m)⁻¹) * ((2 * n).choose m : ℂ) -
        (((w ^ 3) ^ n)⁻¹ * (w ^ 3) ^ m) * ((2 * n).choose m : ℂ) := by
    intro m
    ring
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    gS1, gS2, gS3, gS4]
  ring

/-- Closed form for the Kronecker-symbol side. -/
private theorem kron_sum_closed (s w : ℂ) (hs2 : s ^ 2 = 2) (hs0 : s ≠ 0)
    (hw : w = (1 + Complex.I) / s) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k % 2 = 0 then (0 : ℂ)
        else if k % 8 = 1 ∨ k % 8 = 7 then (1 : ℂ) else (-1 : ℂ)) *
      ((2 * n).choose (n + k) : ℂ) = ((2 + s) ^ n - (2 - s) ^ n) / (2 * s) := by
  have h2s : (2 : ℂ) * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have hw0 : w ≠ 0 := by
    have h1I : (1 : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : ((1 : ℂ) + Complex.I).im = ((0 : ℂ)).im := congrArg Complex.im h
      rw [Complex.add_im, Complex.one_im, Complex.I_im, Complex.zero_im] at him
      norm_num at him
    rw [hw]
    exact div_ne_zero h1I hs0
  have hF := kron_filter s w hs2 hs0 hw
  have e : ∀ k : ℕ,
      (if k % 2 = 0 then (0 : ℂ)
        else if k % 8 = 1 ∨ k % 8 = 7 then (1 : ℂ) else (-1 : ℂ)) *
        ((2 * n).choose (n + k) : ℂ) =
      ((w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) / (2 * s) := by
    intro k
    have hk := hF k
    rw [eq_div_iff h2s]
    linear_combination ((2 * n).choose (n + k) : ℂ) * hk
  have hV : (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) = (2 + s) ^ n - (2 - s) ^ n := by
    have hS := kron_symm w hw0 n
    have hG := kron_geom s w hs2 hs0 hw n
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
          (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
          ((2 * n).choose (n + k) : ℂ)) = 2 * ((2 + s) ^ n - (2 - s) ^ n) := by
      rw [hS]
      exact hG
    exact mul_left_cancel₀ two_ne_zero h2
  calc (∑ k ∈ Finset.range (n + 1),
        (if k % 2 = 0 then (0 : ℂ)
          else if k % 8 = 1 ∨ k % 8 = 7 then (1 : ℂ) else (-1 : ℂ)) *
        ((2 * n).choose (n + k) : ℂ))
      = ∑ k ∈ Finset.range (n + 1),
        ((w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
          ((2 * n).choose (n + k) : ℂ)) / (2 * s) :=
        Finset.sum_congr rfl (fun k _ => e k)
    _ = (∑ k ∈ Finset.range (n + 1),
        (w ^ k + (w ^ k)⁻¹ - w ^ (3 * k) - (w ^ (3 * k))⁻¹) *
        ((2 * n).choose (n + k) : ℂ)) / (2 * s) :=
        (Finset.sum_div _ _ _).symm
    _ = ((2 + s) ^ n - (2 - s) ^ n) / (2 * s) := by rw [hV]

/--
**Binomial transform of the Pell numbers.** Let $P \colon \mathbb{N} \to \mathbb{Z}$ satisfy
$P_0 = 0$, $P_1 = 1$ and $P_{n+2} = 2 P_{n+1} + P_n$ for every $n$, so that $P_n$ is the
$n$-th Pell number. Then for every natural number $n$,
$$\sum_{i=0}^{n} \binom{n}{i} P_i = \sum_{k=0}^{n} \left(\frac{k}{8}\right) \binom{2n}{n+k},$$
where $\left(\frac{k}{8}\right)$ is the Kronecker symbol: it is $0$ for even $k$, $1$ for
$k \equiv \pm 1 \pmod 8$ and $-1$ for $k \equiv \pm 3 \pmod 8$.

Both sides give $0, 1, 4, 14, 48, 164, \dots$ (OEIS A007070) for $n = 0, \dots, 5$.

Proves `Wanted` entry `pell_binomial_transform`.

Source: Greg Dresden and Yike Li, "Periodic Weighted Sums of Binomial
Coefficients," Journal of Integer Sequences 26 (2023), Article 23.8.7,
Corollary (equation e.12), lines 369–379,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.tex
-/
theorem pell_binomial_transform
    (P : ℕ → ℤ) (h0 : P 0 = 0) (h1 : P 1 = 1)
    (hrec : ∀ n, P (n + 2) = 2 * P (n + 1) + P n) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * P i =
    ∑ k ∈ Finset.range (n + 1),
      (if k % 2 = 0 then (0 : ℤ) else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1) *
      ((2 * n).choose (n + k) : ℤ) := by
  have hs2 : (((Real.sqrt 2 : ℝ)) : ℂ) ^ 2 = 2 := by
    have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    exact_mod_cast h
  have hs0 : (((Real.sqrt 2 : ℝ)) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs2
    norm_num at hs2
  have hQ : ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * P i : ℤ) : ℂ) =
      ((2 + ((Real.sqrt 2 : ℝ) : ℂ)) ^ n - (2 - ((Real.sqrt 2 : ℝ) : ℂ)) ^ n) /
      (2 * ((Real.sqrt 2 : ℝ) : ℂ)) := by
    push_cast
    exact pell_binom_closed P h0 h1 hrec _ hs2 n
  have hS : ((∑ k ∈ Finset.range (n + 1),
      (if k % 2 = 0 then (0 : ℤ)
        else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1) *
      ((2 * n).choose (n + k) : ℤ) : ℤ) : ℂ) =
      ((2 + ((Real.sqrt 2 : ℝ) : ℂ)) ^ n - (2 - ((Real.sqrt 2 : ℝ) : ℂ)) ^ n) /
      (2 * ((Real.sqrt 2 : ℝ) : ℂ)) := by
    push_cast
    exact kron_sum_closed _ _ hs2 hs0 rfl n
  have hcast : ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * P i : ℤ) : ℂ) =
      ((∑ k ∈ Finset.range (n + 1),
        (if k % 2 = 0 then (0 : ℤ)
          else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1) *
        ((2 * n).choose (n + k) : ℤ) : ℤ) : ℂ) := by
    rw [hQ, hS]
  exact Int.cast_injective hcast

end MetaMathlibExt
