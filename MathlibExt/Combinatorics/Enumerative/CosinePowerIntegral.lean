/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central

/-!
# The cosine-power integral in Knuth's old sum

Odd powers integrate to zero. For even powers, the cosine reduction formula and the
central binomial coefficient recurrence give the same factor at each step.
-/

namespace MetaMathlibExt

/-- **Integral of $\cos^m x$ over $[0, \pi]$.** For every natural number $m$,
$\int_0^\pi \cos^m x \, dx$ equals $\pi \binom{m}{m/2} / 2^m$ if $m$ is even and $0$ if $m$ is
odd.

This is equation (9) of the source.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem integral_cos_pow_zero_pi (m : ℕ) :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ m =
      if Even m then Real.pi * (m.choose (m / 2) : ℝ) / 2 ^ m else 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [ite_eq_left (even_two_mul k), Nat.mul_div_cancel_left k Nat.zero_lt_two,
      ← Nat.centralBinom_eq_two_mul_choose, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, integral_cos_pow]
      simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_zero, zero_div, zero_add, ih,
        Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      have h : ((k : ℝ) + 1) * ((k + 1).centralBinom : ℝ) =
          2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ k
      have hstep : ((k + 1).centralBinom : ℝ) =
          2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) / ((k : ℝ) + 1) :=
        (eq_div_iff (by positivity)).mpr ((mul_comm _ _).trans h)
      rw [hstep]
      field_simp
      ring
  · rw [ite_eq_right (Nat.not_even_two_mul_add_one k)]
    simpa only [Nat.mul_zero, pow_zero, one_mul, Real.sin_zero, Real.sin_pi,
      intervalIntegral.integral_same] using
      (integral_sin_pow_mul_cos_pow_odd (a := 0) (b := Real.pi) 0 k)

end MetaMathlibExt
