/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomialProductAsymptotics
import MathlibExt.NumberTheory.CentralBinomialProductAsymptotics

/-!
# Hirschhorn's constant

The normalized product of the ratios of factorials to their Stirling approximations converges
to the first factorial product constant. We express the logarithm of the product in terms of
the log factorial and the weighted sum of logarithms, then use their Euler–Maclaurin estimates.
-/

namespace MetaMathlibExt

open Filter Topology
open LogFactorialExpansion

namespace tendsto_hirschhorn_constant

private noncomputable def stirlingRatio (k : ℕ) : ℝ :=
  k.factorial / (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k)

private theorem stirlingRatio_pos {k : ℕ} (hk : 0 < k) : 0 < stirlingRatio k := by
  unfold stirlingRatio
  positivity

private theorem log_stirlingRatio {k : ℕ} (hk : 0 < k) :
    Real.log (stirlingRatio k) = Real.log k.factorial -
      (Real.log (2 * Real.pi) + Real.log k) / 2 - k * (Real.log k - 1) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold stirlingRatio
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_mul (by positivity) hk'.ne', Real.log_pow,
    Real.log_div hk'.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

-- In the product of factorials each log k occurs n + 1 - k times.
private theorem log_prod_stirlingRatio (n : ℕ) :
    Real.log (∏ k ∈ Finset.Icc 1 n, stirlingRatio k) =
      (n + 1 / 2 : ℝ) * Real.log n.factorial - 2 * weightedLog n -
        n / 2 * Real.log (2 * Real.pi) + n * (n + 1) / 2 := by
  induction n with
  | zero => simp [weightedLog]
  | succ n ih =>
    have hp := Finset.prod_pos (s := Finset.Icc 1 n) fun k hk =>
      stirlingRatio_pos (Finset.mem_Icc.mp hk).1
    rw [Finset.prod_Icc_succ_top (by omega), Real.log_mul hp.ne' (stirlingRatio_pos (by omega)).ne',
      ih, log_stirlingRatio (by omega), weightedLog_succ, log_factorial_succ, Nat.cast_add_one]
    ring

private theorem log_error {n : ℕ} (hn : 0 < n) :
    Real.log ((n : ℝ) ^ (-(1 : ℝ) / 12) * ∏ k ∈ Finset.Icc 1 n, stirlingRatio k) -
        Real.log (factorialProductConstant 1) =
      n * factorialError n + factorialError n / 2 - 2 * weightedError n +
        (1 / 24) * (n : ℝ)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := Finset.prod_pos (s := Finset.Icc 1 n) fun k hk =>
    stirlingRatio_pos (Finset.mem_Icc.mp hk).1
  rw [Real.log_mul (by positivity) hp.ne', Real.log_rpow hn', log_prod_stirlingRatio,
    log_factorialProductConstant_one]
  unfold factorialError factorialMain weightedError weightedMain
  field_simp
  ring

private theorem product_limit :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 12) * ∏ k ∈ Finset.Icc 1 n, stirlingRatio k)
      atTop (𝓝 (factorialProductConstant 1)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he := (((error_limits.1.add (factorialError_limit.div_const 2)).sub
    (error_limits.2.const_mul 2)).add (hi.const_mul (1 / 24))).add_const
      (Real.log (factorialProductConstant 1))
  have hl := Real.continuous_exp.continuousAt.tendsto.comp he
  simp only [zero_div, mul_zero, add_zero, sub_zero, zero_add,
    Real.exp_log (factorialProductConstant_pos 1)] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_apply]
  rw [← log_error hn, sub_add_cancel, Real.exp_log]
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
    (Finset.prod_pos fun k hk => stirlingRatio_pos (Finset.mem_Icc.mp hk).1)

end tendsto_hirschhorn_constant

open tendsto_hirschhorn_constant

/-- **Hirschhorn's constant.** Let $A$ be the Glaisher–Kinkelin constant and $F_1$ the first
factorial product constant. As $n \to \infty$,
$$n^{-1/12} \prod_{k=1}^{n} \frac{k!}{\sqrt{2\pi k}\,(k/e)^k}
\to \frac{(2\pi)^{1/4} e^{1/12}}{A^2},$$
and this limit equals $F_1$.

Hirschhorn's asymptotic expansion with divergent Bernoulli sums is not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 12 (Hirschhorn) and the discussion
after it; the constant is defined in the Theorem of M. D. Hirschhorn, "The asymptotic
behavior of $\prod_{k=0}^{n} \binom{n}{k}$", Fibonacci Quart. 51 (2013), 163–173. -/
public theorem tendsto_hirschhorn_constant :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 12) *
        ∏ k ∈ Finset.Icc 1 n, ((k.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k)))
      atTop (𝓝 ((2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) /
        glaisherKinkelinConstant ^ 2)) ∧
    (2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) / glaisherKinkelinConstant ^ 2 =
      factorialProductConstant 1 := by
  have hA : 0 < glaisherKinkelinConstant := Real.exp_pos _
  have hc : (2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) / glaisherKinkelinConstant ^ 2 =
      factorialProductConstant 1 := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (factorialProductConstant_pos 1)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_exp, Real.log_pow, log_factorialProductConstant_one]
    norm_num
  exact ⟨hc ▸ product_limit, hc⟩

end MetaMathlibExt
