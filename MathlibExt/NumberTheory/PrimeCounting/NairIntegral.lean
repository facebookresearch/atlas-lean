/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Nair's integral

Expanding `xⁿ(1 - x)ⁿ` binomially shows that `∫₀¹ xⁿ(1 - x)ⁿ dx` is a rational number whose
denominator divides `lcm(1, …, 2n+1) = e^{ψ(2n+1)}`. This is the starting point of Nair's
elementary lower bound for Chebyshev's function.

## Main statements

* `Nat.exists_pos_eq_lcmUpto_mul_integral`: `lcm(1, …, 2n+1) ∫₀¹ xⁿ(1 - x)ⁿ dx` is a positive
  integer
* `Chebyshev.exists_pos_eq_exp_psi_mul_integral`: `e^{ψ(2n+1)} ∫₀¹ xⁿ(1 - x)ⁿ dx` is a positive
  integer
-/

@[expose] public section

open scoped Chebyshev

namespace Nat

/-- `lcm(1, …, 2n+1) ∫₀¹ xⁿ(1 - x)ⁿ dx` is a positive integer. -/
theorem exists_pos_eq_lcmUpto_mul_integral (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧
      (lcmUpto (2 * n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n = m := by
  have hdvd : ∀ k ∈ Finset.range (n + 1), (n + k + 1) ∣ lcmUpto (2 * n + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    exact Finset.dvd_lcm (f := id) (by simp only [Finset.mem_Icc]; omega)
  -- Expand `(1 - x)^n` binomially and integrate term by term.
  have hint : (∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n)
      = ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k) / ((n : ℝ) + k + 1) := by
    have hfun : ∀ x : ℝ, x ^ n * (1 - x) ^ n
        = ∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ k * (n.choose k)) * x ^ (n + k) := by
      intro x
      rw [show (1 - x : ℝ) = -x + 1 by ring, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one, neg_pow, pow_add]
      ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      simp
      ring
    · exact fun i _ => Continuous.intervalIntegrable (by fun_prop) 0 1
  -- The integrand is positive on `(0, 1)`, so the integral is positive.
  have hpos : 0 < ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) 0 1) (fun x hx => ?_) zero_lt_one
    exact mul_pos (pow_pos hx.1 n) (pow_pos (by linarith [hx.2]) n)
  -- Multiplying the expansion by the lcm clears every denominator.
  set z : ℤ := ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((lcmUpto (2 * n + 1) / (n + k + 1) : ℕ) : ℤ) with hzdef
  have hz : (z : ℝ) = (lcmUpto (2 * n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n := by
    rw [hint, Finset.mul_sum, hzdef, Int.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hne : ((n + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((lcmUpto (2 * n + 1) / (n + k + 1) : ℕ) : ℝ)
        = (lcmUpto (2 * n + 1) : ℝ) / ((n : ℝ) + k + 1) := by
      rw [Nat.cast_div (hdvd k hk) hne]
      push_cast
      ring
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, hcast]
    ring
  have hzpos : 0 < z := by
    have : (0 : ℝ) < (z : ℝ) := by
      rw [hz]
      exact mul_pos (by exact_mod_cast lcmUpto_pos (2 * n + 1)) hpos
    exact_mod_cast this
  refine ⟨z.toNat, by omega, ?_⟩
  rw [← hz]
  exact_mod_cast (Int.toNat_of_nonneg hzpos.le).symm

end Nat

namespace Chebyshev

/-- **Nair's integral.** `e^{ψ(2n+1)} ∫₀¹ xⁿ(1 - x)ⁿ dx` is a positive integer, where `ψ` is
Chebyshev's function. -/
theorem exists_pos_eq_exp_psi_mul_integral (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧
      Real.exp (ψ (2 * n + 1)) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n = m := by
  have hexp : Real.exp (ψ (2 * (n : ℝ) + 1)) = (Nat.lcmUpto (2 * n + 1) : ℝ) := by
    rw [show (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring, psi_eq_log_lcmUpto,
      Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos (2 * n + 1))]
  rw [hexp]
  exact Nat.exists_pos_eq_lcmUpto_mul_integral n

end Chebyshev
