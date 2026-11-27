/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.HalfIntegerShifts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # The Gamma function at half-integer shifts: special values and a reflection product -/

namespace MathlibExtTest.Analysis.SpecialFunctions.Gamma.HalfIntegerShifts

open MetaMathlibExt

-- No natural number is a negative integer, so the first identity applies at every natural `n`.
private theorem natCast_ne_neg (n m : ℕ) : (n : ℂ) ≠ -((m : ℂ) + 1) := by
  intro h
  have h' : ((n + m + 1 : ℕ) : ℂ) = 0 := by
    push_cast
    linear_combination h
  exact absurd (Nat.cast_eq_zero.mp h') (by omega)

-- `r = 0` in the first identity: `Γ(1/2) = √π`.
example : Complex.Gamma (1 / 2) = Real.sqrt Real.pi := by
  simpa using Gamma_add_half_and_Gamma_half_sub_nat.1 0 (by exact_mod_cast natCast_ne_neg 0)

-- `r = 1` in the first identity: `Γ(3/2) = √π / 2`.
example : Complex.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Gamma_add_half_and_Gamma_half_sub_nat.1 1 (by exact_mod_cast natCast_ne_neg 1)
  rw [show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num, show (2 : ℂ) * 1 = 2 by norm_num,
    show (2 : ℂ) + 1 = 3 by norm_num, show (1 : ℂ) + 1 = 2 by norm_num] at h
  rw [h]
  norm_num
  ring

-- `r = -1/2` is allowed in the first identity; there both sides vanish, as `Γ(0) = 0`.
example : (Real.sqrt Real.pi : ℂ) / (2 : ℂ) ^ (2 * (-1 / 2 : ℂ)) *
    (Complex.Gamma (2 * (-1 / 2) + 1) / Complex.Gamma (-1 / 2 + 1)) = 0 := by
  have hr (m : ℕ) : (-1 / 2 : ℂ) ≠ -((m : ℂ) + 1) := by
    intro h
    have h' : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination 2 * h
    exact absurd (Nat.cast_eq_zero.mp h') (by omega)
  rw [← Gamma_add_half_and_Gamma_half_sub_nat.1 _ hr]
  norm_num

-- `r = 0, 1, 2` in the second identity: `Γ(1/2) = √π`, `Γ(-1/2) = -2√π`, `Γ(-3/2) = 4√π/3`.
example : Complex.Gamma (1 / 2) = Real.sqrt Real.pi := by
  simpa using Gamma_add_half_and_Gamma_half_sub_nat.2 0

example : Complex.Gamma (-1 / 2) = -2 * Real.sqrt Real.pi := by
  have h := Gamma_add_half_and_Gamma_half_sub_nat.2 1
  rw [show (1 / 2 : ℂ) - ((1 : ℕ) : ℂ) = -1 / 2 by norm_num] at h
  rw [h]
  norm_num
  ring

example : Complex.Gamma (-3 / 2) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Gamma_add_half_and_Gamma_half_sub_nat.2 2
  rw [show (1 / 2 : ℂ) - ((2 : ℕ) : ℂ) = -3 / 2 by norm_num,
    show Nat.choose (2 * 2) 2 = 6 by rfl] at h
  rw [h]
  norm_num
  ring

-- Together the two identities give `Γ(n + 1/2) Γ(1/2 - n) = (-1)^n π` for natural `n`.
example (n : ℕ) :
    Complex.Gamma (n + 1 / 2) * Complex.Gamma (1 / 2 - n) = (-1) ^ n * Real.pi := by
  obtain ⟨h₁, h₂⟩ := Gamma_add_half_and_Gamma_half_sub_nat
  have hfac : ((2 * n).factorial : ℂ) = (2 * n).choose n * n.factorial * n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    exact_mod_cast h.symm
  have hpow : (2 : ℂ) ^ (2 * (n : ℂ)) = 2 ^ (2 * n) := by
    exact_mod_cast Complex.cpow_natCast 2 (2 * n)
  have hΓ₁ : Complex.Gamma (2 * n + 1) = (2 * n).factorial := by
    exact_mod_cast Complex.Gamma_nat_eq_factorial (2 * n)
  have hπ : (Real.sqrt Real.pi : ℂ) * Real.sqrt Real.pi = Real.pi := by
    exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
  have hA : ((2 * n).choose n : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hF : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [h₁ n (natCast_ne_neg n), h₂, hpow, hΓ₁, Complex.Gamma_nat_eq_factorial, hfac, ← hπ]
  field_simp

end MathlibExtTest.Analysis.SpecialFunctions.Gamma.HalfIntegerShifts
