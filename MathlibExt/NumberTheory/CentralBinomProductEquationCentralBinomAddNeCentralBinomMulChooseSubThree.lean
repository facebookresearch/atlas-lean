/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
import MathlibExt.NumberTheory.CentralBinomProductEquationSmall

import Mathlib.Tactic.Ring

/-!
# Solvability of `C(2k, k) = C(2a, a) C(x + 2b, b)`

The case `x = a - 3` of Meaghan Allen, *Solvability of
$\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*, INTEGERS 26 (2026), Article A26
(arXiv 2406.10404), with `k = a + b` substituted and `C(2k, k)` written as
`Nat.centralBinom`. The proof compares both sides with binomial recurrences in `b`, and
handles the remaining small values of `b` with the small-case theorem.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem choose_step (a b : ℕ) (ha : 3 ≤ a) :
    (a + 2 * (b + 1) - 3).choose (b + 1) * ((b + 1) * (a + b - 2)) =
      (a + 2 * b - 3).choose b * ((a + 2 * b - 2) * (a + 2 * b - 1)) := by
  let n := a + 2 * b - 3
  rw [show a + 2 * (b + 1) - 3 = n + 2 by dsimp [n]; omega,
    show a + 2 * b - 2 = n + 1 by dsimp [n]; omega,
    show a + 2 * b - 1 = n + 2 by dsimp [n]; omega]
  change (n + 2).choose (b + 1) * ((b + 1) * (a + b - 2)) =
    n.choose b * ((n + 1) * (n + 2))
  rw [← mul_assoc, ← Nat.add_one_mul_choose_eq, mul_assoc,
    show a + b - 2 = n + 1 - b by dsimp [n]; omega, ← Nat.choose_mul_succ_eq]
  ac_rfl

private theorem lt_step (a b : ℕ) (ha : 3 ≤ a)
    (hg : (b + 1) * (a + b - 2) * (2 * (2 * (a + b) + 1)) <
      (a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1)))
    (h : (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b - 3).choose b) :
    (a + (b + 1)).centralBinom < a.centralBinom * (a + 2 * (b + 1) - 3).choose (b + 1) := by
  rw [show a + (b + 1) = a + b + 1 by omega]
  apply Nat.lt_of_mul_lt_mul_left (a := (b + 1) * (a + b - 2) * (a + b + 1))
  calc
    _ = ((b + 1) * (a + b - 2) * (2 * (2 * (a + b) + 1))) *
        (a + b).centralBinom := by
      rw [mul_assoc, Nat.succ_mul_centralBinom_succ]
      ac_rfl
    _ < ((a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1))) *
        (a + b).centralBinom := Nat.mul_lt_mul_of_pos_right hg (Nat.centralBinom_pos _)
    _ ≤ ((a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1))) *
        (a.centralBinom * (a + 2 * b - 3).choose b) := Nat.mul_le_mul_left _ h
    _ = ((a + b + 1) * a.centralBinom) *
        ((a + 2 * b - 3).choose b * ((a + 2 * b - 2) * (a + 2 * b - 1))) := by ac_rfl
    _ = _ := by rw [← choose_step a b ha]; ac_rfl

private theorem gt_step (a b : ℕ) (ha : 3 ≤ a)
    (hg : (a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1)) <
      (b + 1) * (a + b - 2) * (2 * (2 * (a + b) + 1)))
    (h : a.centralBinom * (a + 2 * b - 3).choose b ≤ (a + b).centralBinom) :
    a.centralBinom * (a + 2 * (b + 1) - 3).choose (b + 1) < (a + (b + 1)).centralBinom := by
  rw [show a + (b + 1) = a + b + 1 by omega]
  apply Nat.lt_of_mul_lt_mul_left (a := (b + 1) * (a + b - 2) * (a + b + 1))
  calc
    _ = ((a + b + 1) * a.centralBinom) *
        ((a + 2 * (b + 1) - 3).choose (b + 1) * ((b + 1) * (a + b - 2))) := by ac_rfl
    _ = ((a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1))) *
        (a.centralBinom * (a + 2 * b - 3).choose b) := by rw [choose_step a b ha]; ac_rfl
    _ ≤ ((a + b + 1) * ((a + 2 * b - 2) * (a + 2 * b - 1))) *
        (a + b).centralBinom := Nat.mul_le_mul_left _ h
    _ < ((b + 1) * (a + b - 2) * (2 * (2 * (a + b) + 1))) *
        (a + b).centralBinom := Nat.mul_lt_mul_of_pos_right hg (Nat.centralBinom_pos _)
    _ = _ := by
      rw [mul_assoc, ← Nat.succ_mul_centralBinom_succ]
      ac_rfl

private theorem a_step (a b : ℕ) (ha : 3 ≤ a) (hb : 0 < b)
    (h : (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b - 3).choose b) :
    (a + 1 + b).centralBinom < (a + 1).centralBinom * (a + 1 + 2 * b - 3).choose b := by
  let k := a + b
  let n := a + 2 * b - 3
  change k.centralBinom ≤ a.centralBinom * n.choose b at h
  rw [show a + 1 + b = k + 1 by omega,
    show a + 1 + 2 * b - 3 = n + 1 by dsimp [n]; omega]
  have hc : n.choose b * (n + 1) = (n + 1).choose b * (k - 2) := by
    rw [Nat.choose_mul_succ_eq, show n + 1 - b = k - 2 by dsimp [n, k]; omega]
  have hg : (a + 1) * (k - 2) * (2 * (2 * k + 1)) <
      (2 * (2 * a + 1)) * (n + 1) * (k + 1) := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' ha
    dsimp [k, n]
    rw [show c + 3 + b - 2 = c + 1 + b by omega,
      show c + 3 + 2 * b - 3 = c + 2 * b by omega]
    ring_nf
    omega
  apply Nat.lt_of_mul_lt_mul_left (a := (a + 1) * (k - 2) * (k + 1))
  calc
    _ = ((a + 1) * (k - 2) * (2 * (2 * k + 1))) * k.centralBinom := by
      rw [mul_assoc, Nat.succ_mul_centralBinom_succ]
      ac_rfl
    _ < ((2 * (2 * a + 1)) * (n + 1) * (k + 1)) * k.centralBinom :=
      Nat.mul_lt_mul_of_pos_right hg (Nat.centralBinom_pos _)
    _ ≤ ((2 * (2 * a + 1)) * (n + 1) * (k + 1)) * (a.centralBinom * n.choose b) :=
      Nat.mul_le_mul_left _ h
    _ = ((2 * (2 * a + 1)) * a.centralBinom) * (n.choose b * (n + 1)) * (k + 1) := by ac_rfl
    _ = _ := by rw [← Nat.succ_mul_centralBinom_succ, hc]; ac_rfl

private theorem lt_of_six_le (a b : ℕ) (ha : 6 ≤ a) (hb : 6 ≤ b) :
    (a + b).centralBinom < a.centralBinom * (a + 2 * b - 3).choose b := by
  have hbase : (6 + b).centralBinom < (6 : ℕ).centralBinom * (6 + 2 * b - 3).choose b := by
    induction b, hb using Nat.le_induction with
    | base =>
      simp only [Nat.centralBinom, Nat.choose_eq_fast_choose]
      decide +kernel
    | succ b _ ih =>
      apply lt_step 6 b (by decide) _ ih.le
      rw [show 6 + b - 2 = b + 4 by omega,
        show 6 + 2 * b - 2 = 2 * b + 4 by omega,
        show 6 + 2 * b - 1 = 2 * b + 5 by omega]
      ring_nf
      omega
  induction a, ha using Nat.le_induction with
  | base => exact hbase
  | succ a ha ih => exact a_step a b (by omega) (by omega) ih.le

private theorem gt_of_three_or_four (a b : ℕ) (ha : a = 3 ∨ a = 4) (hb : a ≤ b) :
    a.centralBinom * (a + 2 * b - 3).choose b < (a + b).centralBinom := by
  induction b, hb using Nat.le_induction with
  | base =>
    rcases ha with rfl | rfl <;> decide
  | succ b hb ih =>
    apply gt_step a b (by omega) _ ih.le
    rcases ha with rfl | rfl
    · rw [show 3 + b - 2 = b + 1 by omega,
        show 3 + 2 * b - 2 = 2 * b + 1 by omega,
        show 3 + 2 * b - 1 = 2 * b + 2 by omega]
      ring_nf
      omega
    · rw [show 4 + b - 2 = b + 2 by omega,
        show 4 + 2 * b - 2 = 2 * b + 2 by omega,
        show 4 + 2 * b - 1 = 2 * b + 3 by omega]
      ring_nf
      omega

private theorem gt_of_fifty_nine_le (b : ℕ) (hb : 59 ≤ b) :
    (5 : ℕ).centralBinom * (5 + 2 * b - 3).choose b < (5 + b).centralBinom := by
  induction b, hb using Nat.le_induction with
  | base =>
    simp only [Nat.centralBinom, Nat.choose_eq_fast_choose]
    decide +kernel
  | succ b hb ih =>
    apply gt_step 5 b (by decide) _ ih.le
    rw [show 5 + b - 2 = b + 3 by omega,
      show 5 + 2 * b - 2 = 2 * b + 3 by omega,
      show 5 + 2 * b - 1 = 2 * b + 4 by omega]
    ring_nf
    omega

/-- **Central binomial products in the case $x = a - 3$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-3}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 3$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 4 (`integers-2026-A26-lem-4`). -/
public theorem centralBinom_add_ne_centralBinom_mul_choose_sub_three (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 3).choose b := by
  have ha' : 3 ≤ a := by omega
  have hab' : a ≤ b := by omega
  by_cases h6 : 6 ≤ a
  · exact (lt_of_six_le a b h6 (by omega)).ne
  by_cases h5 : a = 5
  · subst a
    by_cases hb : b < 59
    · simpa only [show 5 + 2 * b - 3 = 2 + 2 * b by omega] using
        centralBinom_add_ne_of_two_le_of_small 2 5 b (by decide) (by decide)
          (by omega) (by omega) (by omega)
    · exact (gt_of_fifty_nine_le b (by omega)).ne'
  exact (gt_of_three_or_four a b (by omega) hab').ne'

end

end MetaMathlibExt
