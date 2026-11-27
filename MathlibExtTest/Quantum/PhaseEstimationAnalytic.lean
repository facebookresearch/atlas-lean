/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Quantum.PhaseEstimationAnalytic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for the phase estimation analytic bound
-/

public section

open BigOperators Real MathlibExt.Quantum.PhaseEstimationAnalytic

namespace MathlibExtTest.Quantum.PhaseEstimationAnalytic

/-- `N = 1`: the amplitude is always one. -/
theorem peAmp_one_eq_one (δ : ℝ) : peAmp 1 δ = 1 := by
  have hexp : ∀ y ∈ Finset.range 1, Complex.exp (2*π*Complex.I*δ*y) = 1 := by
    intro y hy
    rw [Finset.mem_range, Nat.lt_one_iff] at hy
    subst hy
    rw [show (2*π*Complex.I*δ*((0:ℕ)):ℂ) = 0 from by simp, Complex.exp_zero]
  have h1 : ((1 : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_one]
    exact one_ne_zero
  simp only [peAmp]
  rw [Finset.sum_congr rfl hexp, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  exact one_div_mul_cancel h1

/-- `N = 2`, `δ = 1 / 4`: the squared norm equals `1 / 2`. -/
theorem normSq_peAmp_two_quarter : ‖peAmp 2 (1 / 4)‖ ^ 2 = 1 / 2 := by
  have hf0 : Complex.exp (2*π*Complex.I*(1/4:ℝ)*(0:ℕ)) = 1 := by
    rw [show (2*π*Complex.I*(1/4:ℝ)*((0:ℕ)):ℂ) = 0 from by simp, Complex.exp_zero]
  have hf1 : Complex.exp (2*π*Complex.I*(1/4:ℝ)*(1:ℕ)) = Complex.I := by
    have harg : (2*π*Complex.I*(1/4:ℝ)*((1:ℕ)):ℂ) = ((π/2:ℝ):ℂ)*Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hsum : (∑ y ∈ Finset.range 2, Complex.exp (2*π*Complex.I*(1/4:ℝ)*y)) =
      Complex.exp (2*π*Complex.I*(1/4:ℝ)*(0:ℕ)) +
      Complex.exp (2*π*Complex.I*(1/4:ℝ)*(1:ℕ)) := by
    have h := Finset.sum_range_succ (fun y => Complex.exp (2*π*Complex.I*(1/4:ℝ)*y)) 1
    rw [Finset.sum_range_one] at h
    exact h
  have hval : peAmp 2 (1 / 4) = (1 + Complex.I) / 2 := by
    have h2c : ((2 : ℕ) : ℂ) = 2 := by norm_cast
    simp only [peAmp]
    rw [hsum, hf0, hf1, h2c]
    ring
  have e : ((1 + Complex.I) / 2 : ℂ) = ((1/2:ℝ):ℂ) + ((1/2:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [hval, e, Complex.sq_norm, Complex.normSq_add_mul_I]
  norm_num

/-- The bound for `N = 2 ^ m` at `m = 1`, `δ = 1 / 4`, rewritten with the exact value `1 / 2`
of `normSq_peAmp_two_quarter`. -/
theorem four_div_pi_sq_le_half : 4 / π ^ 2 ≤ 1 / 2 := by
  have h := four_div_pi_sq_le_normSq_peAmp_two_pow 1 (1 / 4) (by norm_num) (by norm_num)
  rwa [pow_one, normSq_peAmp_two_quarter] at h

/-- The general bound at `δ = 0`, rewritten with `peAmp_zero`: `4 / π ^ 2 ≤ 1`. -/
theorem four_div_pi_sq_le_one_of_offset_zero (N : ℕ) (hN : 0 < N) : 4 / π ^ 2 ≤ 1 := by
  have h := four_div_pi_sq_le_normSq_peAmp N hN 0 (by rw [abs_zero]; positivity)
  rwa [peAmp_zero N hN, norm_one, one_pow] at h

#print axioms norm_one_sub_exp_ge
#print axioms peAmp_eq_div
#print axioms four_div_pi_sq_le_normSq_peAmp_two_pow
#print axioms four_div_pi_sq_le_normSq_peAmp
#print axioms peAmp_zero

end MathlibExtTest.Quantum.PhaseEstimationAnalytic
