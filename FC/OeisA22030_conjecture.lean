/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/22030.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil












namespace OeisA22030






def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

def b (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | 3 => 249
  | n + 4 => 4 * b (n + 3) - b (n + 1) + b n

@[simp] lemma b_zero : b 0 = 4 := rfl
@[simp] lemma b_one : b 1 = 16 := rfl
@[simp] lemma b_two : b 2 = 63 := rfl
@[simp] lemma b_three : b 3 = 249 := rfl
@[simp] lemma b_step (n : ℕ) :
    b (n + 4) = 4 * b (n + 3) - b (n + 1) + b n := by
  rw [b]

lemma b_growth (n : ℕ) : 3 * b n < b (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · norm_num
    · norm_num
    · norm_num [b]
    · rw [show n + 3 + 1 = n + 4 by omega, b_step]
      have h1 : 3 * b (n + 1) < b (n + 2) := by
        convert ih (n + 1) (by omega) using 1 <;> omega
      have h2 : 3 * b (n + 2) < b (n + 3) := by
        convert ih (n + 2) (by omega) using 1 <;> omega
      have hsub : 3 * b (n + 3) < 4 * b (n + 3) - b (n + 1) := by
        apply Nat.lt_sub_of_add_lt
        omega
      exact lt_of_lt_of_le hsub (Nat.le_add_right _ _)

lemma b_pos (n : ℕ) : 0 < b n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := b_growth n
    omega

lemma b_step_int (n : ℕ) :
    (b (n + 4) : ℤ) = 4 * b (n + 3) - b (n + 1) + b n := by
  rw [b_step]
  have h1 : 3 * b (n + 1) < b (n + 2) := by
    convert b_growth (n + 1) using 1 <;> omega
  have h2 : 3 * b (n + 2) < b (n + 3) := by
    convert b_growth (n + 2) using 1 <;> omega
  have hle : b (n + 1) ≤ 4 * b (n + 3) := by omega
  rw [Nat.cast_add, Nat.cast_sub hle]
  push_cast
  ring


def err (n : ℕ) : ℤ :=
  if n < 2 then 0 else (b (n - 1) : ℤ) ^ 2 - b (n - 2) * b n

lemma err_initial :
    err 2 = 4 ∧ err 3 = -15 ∧ err 4 = 9 ∧ err 5 = -105 ∧
      err 6 = 241 ∧ err 7 = -405 := by
  norm_num [err, b]

lemma err_shift (n : ℕ) :
    err (n + 2) = (b (n + 1) : ℤ) ^ 2 - b n * b (n + 2) := by
  simp only [err, if_neg (by omega : ¬n + 2 < 2)]
  congr 2 <;> omega

lemma err_recurrence (n : ℕ) :
    err (n + 8) = 3 * err (n + 6) - 15 * err (n + 5) -
      3 * err (n + 4) + err (n + 2) := by
  rw [show n + 8 = (n + 6) + 2 by omega, err_shift,
    show n + 6 = (n + 4) + 2 by omega, err_shift,
    show n + 5 = (n + 3) + 2 by omega, err_shift,
    show n + 4 = (n + 2) + 2 by omega, err_shift, err_shift]
  have h4 : (b (n + 4) : ℤ) = 4 * b (n + 3) - b (n + 1) + b n :=
    b_step_int n
  have h5 : (b (n + 5) : ℤ) = 4 * b (n + 4) - b (n + 2) + b (n + 1) := by
    convert b_step_int (n + 1) using 1 <;> omega
  have h6 : (b (n + 6) : ℤ) = 4 * b (n + 5) - b (n + 3) + b (n + 2) := by
    convert b_step_int (n + 2) using 1 <;> omega
  have h7 : (b (n + 7) : ℤ) = 4 * b (n + 6) - b (n + 4) + b (n + 3) := by
    convert b_step_int (n + 3) using 1 <;> omega
  have h8 : (b (n + 8) : ℤ) = 4 * b (n + 7) - b (n + 5) + b (n + 4) := by
    convert b_step_int (n + 4) using 1 <;> omega
  push_cast at h4 h5 h6 h7 h8 ⊢
  rw [h8, h7, h6, h5, h4]
  ring


def e (k : ℕ) : ℤ := (-1 : ℤ) ^ k * err (k + 2)

lemma e_initial :
    e 0 = 4 ∧ e 1 = 15 ∧ e 2 = 9 ∧ e 3 = 105 ∧ e 4 = 241 ∧ e 5 = 405 := by
  norm_num [e, err, b]

lemma e_recurrence (k : ℕ) :
    e (k + 6) = 3 * e (k + 4) + 15 * e (k + 3) -
      3 * e (k + 2) + e k := by
  simp only [e, Nat.add_assoc]
  rw [err_recurrence k]
  simp only [pow_add]
  norm_num
  ring

lemma e_shape (k : ℕ) :
    0 < e k ∧
      (2 ≤ k → e (k - 2) < e k) ∧
      (4 ≤ k → 2 * e (k - 2) < e k + e (k - 4)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | _ | _ | _ | n
    · norm_num [e, err, b]
    · norm_num [e, err, b]
    · norm_num [e, err, b]
    · norm_num [e, err, b]
    · norm_num [e, err, b]
    · norm_num [e, err, b]
    · change 0 < e (n + 6) ∧
        (2 ≤ n + 6 → e (n + 4) < e (n + 6)) ∧
        (4 ≤ n + 6 → 2 * e (n + 4) < e (n + 6) + e (n + 2))
      have h4 := ih (n + 4) (by omega)
      have h3 := ih (n + 3) (by omega)
      have hp4 : 0 < e (n + 4) := h4.1
      have hp3 : 0 < e (n + 3) := h3.1
      have hf := h4.2.1 (by omega)
      have hs := h4.2.2 (by omega)
      rw [show n + 4 - 2 = n + 2 by omega] at hf hs
      rw [show n + 4 - 4 = n by omega] at hs
      have hr := e_recurrence n
      have hs' : 2 * e (n + 4) < e (n + 6) + e (n + 2) := by
        rw [hr]
        nlinarith
      have hf' : e (n + 4) < e (n + 6) := by
        nlinarith
      have hp' : 0 < e (n + 6) := by
        nlinarith
      exact ⟨hp', fun _ ↦ hf', fun _ ↦ hs'⟩

lemma e_pos_and_bound (k : ℕ) :
    0 < e k ∧ e k ≤ 5 * (3 : ℤ) ^ k := by
  constructor
  · exact (e_shape k).1
  · induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases k with _ | _ | _ | _ | _ | _ | n
      · norm_num [e, err, b]
      · norm_num [e, err, b]
      · norm_num [e, err, b]
      · norm_num [e, err, b]
      · norm_num [e, err, b]
      · norm_num [e, err, b]
      · have h0 := ih n (by omega)
        have h2 := ih (n + 2) (by omega)
        have h3 := ih (n + 3) (by omega)
        have h4 := ih (n + 4) (by omega)
        have hp2 := (e_shape (n + 2)).1
        have hr := e_recurrence n
        rw [show n + 6 = n + 6 by rfl, hr]
        rw [show (3 : ℤ) ^ (n + 6) = 729 * 3 ^ n by ring]
        rw [show (3 : ℤ) ^ (n + 4) = 81 * 3 ^ n by ring] at h4
        rw [show (3 : ℤ) ^ (n + 3) = 27 * 3 ^ n by ring] at h3
        rw [show (3 : ℤ) ^ (n + 2) = 9 * 3 ^ n by ring] at h2
        have hpow : (0 : ℤ) < 3 ^ n := by positivity
        nlinarith

lemma err_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 < (-1 : ℤ) ^ n * err n ∧ |err n| ≤ 5 * (3 : ℤ) ^ (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by omega]
  have h := e_pos_and_bound k
  have heq : (-1 : ℤ) ^ (k + 2) * err (k + 2) = e k := by
    simp only [e, pow_add]
    norm_num
  have habs : |err (k + 2)| = e k := by
    have ha : |((-1 : ℤ) ^ k * err (k + 2))| = |err (k + 2)| := by
      simp [abs_mul]
    have hid : (-1 : ℤ) ^ k * err (k + 2) = e k := rfl
    rw [hid, abs_of_pos h.1] at ha
    exact ha.symm
  rw [heq, habs, Nat.add_sub_cancel]
  exact h

lemma b_lower (k : ℕ) : 4 * 3 ^ k ≤ b k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := b_growth k
    rw [pow_succ]
    omega

lemma b_lower_one (k : ℕ) : 16 * 3 ^ k ≤ b (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := b_growth (k + 1)
    rw [pow_succ]
    have heq : k + 1 + 1 = k.succ + 1 := by omega
    rw [← heq]
    omega

lemma err_lt_b (n : ℕ) (hn : 3 ≤ n) : |err n| < b (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + k = k + 3 by omega, show k + 3 - 2 = k + 1 by omega]
  have he := (err_bounds (k + 3) (by omega)).2
  have hb := b_lower_one k
  have hbz : (16 : ℤ) * 3 ^ k ≤ b (k + 1) := by exact_mod_cast hb
  have hp : (0 : ℤ) < 3 ^ k := by positivity
  rw [show k + 3 - 2 = k + 1 by omega, pow_succ] at he
  norm_num at he ⊢
  omega

lemma b_satisfies_nonlinear (n : ℕ) :
    b (n + 2) = if Even n then
      (b (n + 1) ^ 2 + b n - 1) / b n - 1
    else
      (b (n + 1) ^ 2) / b n + 1 := by
  rcases n with _ | n
  · norm_num [b]
  · split_ifs with hp
    · have hs := (err_bounds (n + 1 + 2) (by omega)).1
      have ha := err_lt_b (n + 1 + 2) (by omega)
      have heq := err_shift (n + 1)
      have heven : Even (n + 1 + 2) := hp.add (by norm_num)
      rw [Even.neg_one_pow heven] at hs
      rw [show n + 1 + 2 - 2 = n + 1 by omega] at ha
      rw [heq] at hs ha
      norm_num at hs
      have hsp : 0 < (b (n + 1 + 1) : ℤ) ^ 2 -
          b (n + 1) * b (n + 1 + 2) := by omega
      have hm : 1 ≤ b (n + 1 + 1) ^ 2 + b (n + 1) := by
        have := b_pos (n + 1)
        omega
      have hloz :
          ((((b (n + 1 + 2) + 1) * b (n + 1) : ℕ) : ℤ)) ≤
            ((b (n + 1 + 1) ^ 2 + b (n + 1) - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hm]
        push_cast
        rw [abs_of_pos hsp] at ha
        nlinarith
      have hhiz :
          ((b (n + 1 + 1) ^ 2 + b (n + 1) - 1 : ℕ) : ℤ) <
            ((((b (n + 1 + 2) + 2) * b (n + 1) : ℕ) : ℤ)) := by
        rw [Nat.cast_sub hm]
        push_cast
        rw [abs_of_pos hsp] at ha
        nlinarith
      have hlo : (b (n + 1 + 2) + 1) * b (n + 1) ≤
          b (n + 1 + 1) ^ 2 + b (n + 1) - 1 := by exact_mod_cast hloz
      have hhi : b (n + 1 + 1) ^ 2 + b (n + 1) - 1 <
          (b (n + 1 + 2) + 2) * b (n + 1) := by exact_mod_cast hhiz
      rw [Nat.div_eq_of_lt_le hlo hhi]
      omega
    · have hs := (err_bounds (n + 1 + 2) (by omega)).1
      have ha := err_lt_b (n + 1 + 2) (by omega)
      have heq := err_shift (n + 1)
      have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp hp
      have hodd' : Odd (n + 1 + 2) := hodd.add_even (by norm_num)
      rw [Odd.neg_one_pow hodd'] at hs
      rw [show n + 1 + 2 - 2 = n + 1 by omega] at ha
      rw [heq] at hs ha
      norm_num at hs
      have hsn : (b (n + 1 + 1) : ℤ) ^ 2 -
          b (n + 1) * b (n + 1 + 2) < 0 := by omega
      have hz := b_pos (n + 1 + 2)
      have hzle : 1 ≤ b (n + 1 + 2) := hz
      have hloz :
          ((((b (n + 1 + 2) - 1) * b (n + 1) : ℕ) : ℤ)) ≤
            ((b (n + 1 + 1) ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub hzle]
        push_cast
        rw [abs_of_neg hsn] at ha
        nlinarith
      have hhiz : ((b (n + 1 + 1) ^ 2 : ℕ) : ℤ) <
          ((((b (n + 1 + 2) - 1 + 1) * b (n + 1) : ℕ) : ℤ)) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hzle]
        push_cast
        rw [abs_of_neg hsn] at ha
        nlinarith
      have hlo : (b (n + 1 + 2) - 1) * b (n + 1) ≤
          b (n + 1 + 1) ^ 2 := by exact_mod_cast hloz
      have hhi : b (n + 1 + 1) ^ 2 <
          (b (n + 1 + 2) - 1 + 1) * b (n + 1) := by exact_mod_cast hhiz
      rw [Nat.div_eq_of_lt_le hlo hhi]
      omega

lemma a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rfl
    · rfl
    · rw [a]
      have h0 : a n = b n := ih n (by omega)
      have h1 : a (n + 1) = b (n + 1) := ih (n + 1) (by omega)
      rw [h0, h1]
      exact (b_satisfies_nonlinear n).symm





@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 4 ≤ n) :
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 4 + k = k + 4 by omega,
    show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 4 = k by omega]
  simp only [a_eq_b]
  exact b_step k

end OeisA22030
