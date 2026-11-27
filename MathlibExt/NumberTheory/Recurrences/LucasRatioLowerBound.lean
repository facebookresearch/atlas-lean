/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Ratios of consecutive Lucas terms

This module proves lower bounds for the ratio of consecutive terms of the fundamental Lucas
sequence for both signs of the second parameter.
-/

namespace MetaMathlibExt

/-- **Lower bounds for ratios of consecutive Lucas terms.** Let $x$ and $y \neq 0$ be integers
with $x \geq 1$ and $|y + 1| \leq x$, and let $(U_n)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. If $y < 0$, then
$U_n / U_{n-1} \geq x - xy/(x^2 - y)$ for every $n > 2$. If $y > 0$, then
$U_n / U_{n-1} \geq (x + \sqrt{x^2 - 4y})/2$ for every $n \geq 2$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.3 (`fq-2024-earplynch07182024-lem-2.3`). -/
public theorem lucasU_ratio_lower_bound (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) :
    (P.q < 0 → ∀ n : ℕ, 2 < n →
      (P.p : ℝ) - P.p * P.q / (P.p ^ 2 - P.q) ≤ (lucasU P n : ℝ) / lucasU P (n - 1)) ∧
    (0 < P.q → ∀ n : ℕ, 2 ≤ n →
      (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2 ≤ (lucasU P n : ℝ) / lucasU P (n - 1)) := by
  let x : ℝ := P.p
  let y : ℝ := P.q
  let U (k : ℕ) : ℝ := lucasU P k
  have hx' : 0 < x := Int.cast_pos.mpr (by omega)
  have recurrence (k : ℕ) : U (k + 2) = x * U (k + 1) - y * U k := by
    dsimp [U, x, y]
    exact_mod_cast lucasU_add_two P k
  constructor
  · intro hneg n hn
    have hy' : y < 0 := Int.cast_lt_zero.mpr hneg
    -- The recurrence gives Uₖ₊₁ ≥ x Uₖ, and every term from U₁ on is positive.
    have growth (k : ℕ) : 0 ≤ U k ∧ 0 < U (k + 1) ∧ x * U k ≤ U (k + 1) := by
      induction k with
      | zero => simp [U, lucasU]
      | succ k ih =>
        have h : x * U (k + 1) ≤ U (k + 2) := by
          rw [recurrence k]
          linarith only [mul_nonpos_of_nonpos_of_nonneg hy'.le ih.1]
        exact ⟨ih.2.1.le, (mul_pos hx' ih.2.1).trans_le h, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ n by omega)
    change x - x * y / (x ^ 2 - y) ≤ U (k + 3) / U (k + 2)
    -- Apply the growth bound to the preceding term to bound Uₖ₊₂ from above.
    have upper : x * U (k + 2) ≤ (x ^ 2 - y) * U (k + 1) := by
      rw [recurrence k]
      nlinarith only [mul_le_mul_of_nonneg_left (growth k).2.2 (neg_nonneg.mpr hy'.le)]
    apply (le_div_iff₀ (growth (k + 1)).2.1).2
    rw [recurrence (k + 1)]
    have hd : 0 < x ^ 2 - y := by linarith only [sq_nonneg x, hy']
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left upper (neg_nonneg.mpr hy'.le)]
  · intro hpos n hn
    have hy' : 0 < y := Int.cast_pos.mpr hpos
    have hxy : y + 1 ≤ x := by
      dsimp [x, y]
      exact_mod_cast (le_abs_self (P.q + 1)).trans hy
    have hd : 0 ≤ x ^ 2 - 4 * y := by nlinarith only [sq_nonneg (x - 2), hxy]
    let α := (x + Real.sqrt (x ^ 2 - 4 * y)) / 2
    have hα : 0 < α :=
      div_pos (add_pos_of_pos_of_nonneg hx' (Real.sqrt_nonneg _)) (by norm_num)
    have hαx : α ≤ x := by
      have hs : Real.sqrt (x ^ 2 - 4 * y) ≤ x := Real.sqrt_le_iff.mpr ⟨hx'.le, by linarith⟩
      dsimp [α]
      linarith
    have hroot : (x - α) * α = y := by
      dsimp [α]
      nlinarith only [Real.sq_sqrt hd]
    -- The difference Uₖ₊₁ - α Uₖ is multiplied by the nonnegative smaller root at each step.
    have growth (k : ℕ) : 0 < U (k + 1) ∧ α * U k ≤ U (k + 1) := by
      induction k with
      | zero => simp [U, lucasU]
      | succ k ih =>
        have h : α * U (k + 1) ≤ U (k + 2) := by
          rw [recurrence k, ← hroot]
          nlinarith only [mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hαx)]
        exact ⟨(mul_pos hα ih.1).trans_le h, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact (le_div_iff₀ (growth k).1).2 (growth (k + 1)).2

end MetaMathlibExt
