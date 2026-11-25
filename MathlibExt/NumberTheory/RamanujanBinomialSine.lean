/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Ramanujan's binomial sine series

We prove the binomial sine series identity for a nonnegative real exponent and angles in
the closed interval from `-π / 2` to `π / 2`.
-/

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

open Complex Metric

private lemma summable_abs_choose {N : ℝ} (hN : 0 < N) :
    Summable (fun n : ℕ => |Ring.choose N n|) := by
  obtain ⟨m, hm⟩ := exists_nat_ge N
  rw [← summable_nat_add_iff m]
  -- On this tail, the weighted absolute coefficients have successive differences
  -- equal to N times the absolute coefficients.
  let b (n : ℕ) := ((n + m : ℕ) : ℝ) * |Ring.choose N (n + m)|
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hstep (n : ℕ) : b n - b (n + 1) = N * |Ring.choose N (n + m)| := by
    have hchoose (k : ℕ) :
        ((k : ℝ) + 1) * Ring.choose N (k + 1) = Ring.choose N k * (N - k) := by
      simpa [Nat.choose_succ_self_right, nsmul_eq_mul, Ring.choose_one_right]
        using Ring.choose_smul_choose N (n := k + 1) (k := k) (Nat.le_succ k)
    have habs := congrArg abs (hchoose (n + m))
    have hle : N ≤ ((n + m : ℕ) : ℝ) :=
      hm.trans (by exact_mod_cast Nat.le_add_left m n)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n + m : ℕ) : ℝ) + 1),
      abs_of_nonpos (sub_nonpos.mpr hle)] at habs
    simp only [b, show n + 1 + m = n + m + 1 by omega, Nat.cast_succ]
    rw [habs]
    ring
  refine summable_of_sum_range_le (c := b 0 / N) (fun n => abs_nonneg _) fun k => ?_
  apply (le_div_iff₀ hN).mpr
  rw [mul_comm, Finset.mul_sum]
  simp_rw [← hstep]
  rw [Finset.sum_range_sub']
  exact sub_le_self _ (hb k)

private lemma hasSum_choose_mul_pow_closedDisk {N : ℝ} (hN : 0 < N) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => ((Ring.choose N n : ℝ) : ℂ) * z ^ n) ((1 + z) ^ (N : ℂ)) := by
  let f (n : ℕ) (w : ℂ) := ((Ring.choose N n : ℝ) : ℂ) * w ^ n
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) :
      ‖f n w‖ ≤ |Ring.choose N n| := by
    rw [mem_closedBall_zero_iff] at hw
    simp only [f, norm_mul, norm_real, Real.norm_eq_abs, norm_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hw)
  have hcont : ContinuousOn (fun w => ∑' n, f n w) (closedBall (0 : ℂ) 1) :=
    continuousOn_tsum (fun n => (by fun_prop : Continuous (f n)).continuousOn)
      (summable_abs_choose hN) hbound
  have hpow : ContinuousOn (fun w : ℂ => (1 + w) ^ (N : ℂ)) (closedBall 0 1) := by
    intro w hw
    have hnorm := mem_closedBall_zero_iff.mp hw
    have hre : 0 ≤ (1 + w).re := by
      rw [add_re, one_re]
      linarith [neg_le_abs w.re, abs_re_le_norm w]
    exact ((continuousAt_cpow_const_of_re_pos (.inl hre) (by simpa using hN)).comp
      (by fun_prop : ContinuousAt (fun w : ℂ => 1 + w) w)).continuousWithinAt
  have hopen : Set.EqOn (fun w => ∑' n, f n w) (fun w : ℂ => (1 + w) ^ (N : ℂ))
      (ball 0 1) := by
    intro w hw
    have hmem : w ∈ eball (0 : ℂ) 1 := by
      simpa only [← ENNReal.coe_one, eball_coe, NNReal.coe_one] using hw
    simpa only [f, binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
      ← ofReal_choose, zero_add] using
      (one_add_cpow_hasFPowerSeriesOnBall_zero (a := (N : ℂ))).hasSum hmem |>.tsum_eq
  have hclosed := hopen.of_subset_closure hcont hpow ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) one_ne_zero])
  have hzmem := mem_closedBall_zero_iff.mpr hz
  simpa only [f, hclosed hzmem] using ((summable_abs_choose hN).of_norm_bounded
    (fun n => hbound n z hzmem)).hasSum

private lemma one_add_exp_two_mul (θ : ℝ) :
    1 + exp (((2 * θ : ℝ) : ℂ) * I) = ((2 * Real.cos θ : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
  have hcos : ((2 * Real.cos θ : ℝ) : ℂ) =
      exp ((θ : ℂ) * I) + exp (-((θ : ℂ) * I)) := by
    rw [ofReal_mul, ofReal_ofNat, ofReal_cos, Complex.cos, neg_mul]
    ring
  rw [hcos, add_mul, ← exp_add, ← exp_add, neg_add_cancel, exp_zero, add_comm]
  congr 2
  push_cast
  ring

private lemma cpow_real_mul_exp {r N θ : ℝ} (hr : 0 ≤ r) (hN : 0 < N)
    (hθ : |θ| ≤ Real.pi / 2) :
    ((r : ℂ) * exp ((θ : ℂ) * I)) ^ (N : ℂ) =
      (↑(r ^ N) : ℂ) * exp (((N * θ : ℝ) : ℂ) * I) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [Complex.zero_cpow (ofReal_ne_zero.mpr hN.ne'), Real.zero_rpow hN.ne']
  have hlog : log (exp ((θ : ℂ) * I)) = (θ : ℂ) * I := by
    apply log_exp <;> simp only [mul_I_im, ofReal_re]
    · linarith [(abs_le.mp hθ).1, Real.pi_pos]
    · linarith [(abs_le.mp hθ).2, Real.pi_pos]
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)),
    log_ofReal_mul hr (exp_ne_zero _), hlog, add_mul, exp_add, Real.rpow_def_of_pos hr,
    ofReal_exp, ofReal_mul]
  congr 2
  push_cast
  ring

/-- **Ramanujan's binomial sine series.** Let $a$, $N$ and $\theta$ be real numbers with
$N \ge 0$ and $|\theta| \le \pi / 2$. Then the series
$\sum_{\nu=0}^{\infty} \binom{N}{\nu} \sin((a + 2\nu)\theta)$ converges unconditionally to
$2^N (\cos \theta)^N \sin((a + N)\theta)$. Here $\binom{N}{\nu} = N(N-1)\cdots(N-\nu+1)/\nu!$
is the generalized binomial coefficient, and $2^N$ and $(\cos \theta)^N$ are real powers.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Lemma 1. -/
public theorem hasSum_ringChoose_mul_sin
    (a N θ : ℝ) (hN : 0 ≤ N) (hθ : |θ| ≤ Real.pi / 2) :
    HasSum
      (fun ν : ℕ => Ring.choose N ν * Real.sin ((a + 2 * (ν : ℝ)) * θ))
      ((2 : ℝ) ^ N * (Real.cos θ) ^ N * Real.sin ((a + N) * θ)) := by
  rcases hN.eq_or_lt with rfl | hN
  · simp only [Real.rpow_zero, one_mul, add_zero]
    refine (hasSum_ite_eq (0 : ℕ) (Real.sin (a * θ))).congr_fun ?_
    intro ν
    by_cases hν : ν = 0 <;> simp [Ring.choose_zero_ite, hν]
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc (abs_le.mp hθ)
  have hsum := hasSum_choose_mul_pow_closedDisk hN
    (z := exp (((2 * θ : ℝ) : ℂ) * I)) (by rw [norm_exp_ofReal_mul_I])
  rw [one_add_exp_two_mul, cpow_real_mul_exp (by positivity) hN hθ,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hcos] at hsum
  have him := hasSum_im (hsum.mul_left (exp (((a * θ : ℝ) : ℂ) * I)))
  convert him using 1
  · ext ν
    rw [← mul_left_comm, ← exp_nat_mul, ← exp_add, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [show ((↑(a * θ) : ℂ) * I + (ν : ℂ) * (↑(2 * θ) * I)) =
      (↑((a + 2 * (ν : ℝ)) * θ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I_im]
  · rw [mul_left_comm, ← exp_add, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [show ((↑(a * θ) : ℂ) * I + (↑(N * θ) : ℂ) * I) =
      (↑((a + N) * θ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I_im]

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
