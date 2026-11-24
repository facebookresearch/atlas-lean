/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Tactic.LinearCombination

/-!
# Pell and Pell–Lucas numbers times the silver ratio

Multiplying an odd-indexed Pell number or an even-indexed Pell–Lucas number by the silver ratio
`1 + √2` gives the next term plus an explicit power of `√2 - 1`, scaled by `√2` for Pell–Lucas.
-/

namespace MetaMathlibExt

private theorem pellNumber_odd_mul_one_add_sqrt_two.recurrence_error (u : ℕ → ℕ)
    (h : ∀ n, u (n + 2) = 2 * u (n + 1) + u n) (n : ℕ) :
    (u n : ℝ) * (1 + Real.sqrt 2) - u (n + 1) =
      ((u 0 : ℝ) * (1 + Real.sqrt 2) - u 1) * (1 - Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ← ih, h]
    push_cast
    linear_combination (u n : ℝ) * Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- **Odd Pell and even Pell–Lucas numbers times $1 + \sqrt 2$.** Let $P_n$ be the Pell numbers and
$H_n$ the Pell–Lucas numbers ($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). For every natural
number $k$, $P_{2k+1}(1 + \sqrt 2) = P_{2k+2} + (\sqrt 2 - 1)^{2k+1}$ and
$H_{2k}(1 + \sqrt 2) = H_{2k+1} + \sqrt 2\,(\sqrt 2 - 1)^{2k}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 2 (1), (2). -/
public theorem pellNumber_odd_mul_one_add_sqrt_two (k : ℕ) :
    (pellNumber (2 * k + 1) : ℝ) * (1 + Real.sqrt 2) =
        pellNumber (2 * k + 2) + (Real.sqrt 2 - 1) ^ (2 * k + 1) ∧
      (pellLucasSequence (2 * k) : ℝ) * (1 + Real.sqrt 2) =
        pellLucasSequence (2 * k + 1) + Real.sqrt 2 * (Real.sqrt 2 - 1) ^ (2 * k) := by
  have hp := pellNumber_odd_mul_one_add_sqrt_two.recurrence_error pellNumber
    (fun _ => rfl) (2 * k + 1)
  have hh := pellNumber_odd_mul_one_add_sqrt_two.recurrence_error pellLucasSequence
    pellLucasSequence_succ_succ (2 * k)
  rw [← neg_sub (Real.sqrt 2) 1, (odd_two_mul_add_one k).neg_pow] at hp
  rw [← neg_sub (Real.sqrt 2) 1, (even_two_mul k).neg_pow] at hh
  simp only [show pellNumber 0 = 0 from rfl, show pellNumber 1 = 1 from rfl,
    Nat.cast_zero, Nat.cast_one, zero_mul, zero_sub, neg_mul, one_mul, neg_neg] at hp
  simp only [pellLucasSequence_zero, pellLucasSequence_one, Nat.cast_one, one_mul,
    add_sub_cancel_left] at hh
  exact ⟨sub_eq_iff_eq_add'.mp hp, sub_eq_iff_eq_add'.mp hh⟩

end MetaMathlibExt
