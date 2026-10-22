/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.InfiniteTaylorSupport
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermAttained
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Interval.Finset.Basic

@[expose] public section

namespace Complex

open Filter

/-- **The maximum term of a transcendental entire function tends to infinity.** Let $f$ be an
entire function that is not a polynomial function, with Taylor coefficients $a_n$ at the origin
and maximum term $\mu(r) = \sup_n |a_n|\,|r|^n$. Then $\mu(r) \to \infty$ as $r \to \infty$. -/
theorem tendsto_wimanMaximumTerm_atTop
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    Tendsto (wimanMaximumTerm f) atTop atTop := by
  obtain ⟨n, hnmem, hnpos⟩ :=
    (infinite_support_wimanTaylorCoefficient f hf htrans).exists_gt 0
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hcoeff : wimanTaylorCoefficient f n ≠ 0 := by
    simpa only [Function.mem_support] using hnmem
  have hcoeffnorm : 0 < ‖wimanTaylorCoefficient f n‖ := norm_pos_iff.mpr hcoeff
  have hterm : Tendsto (fun r : ℝ ↦ wimanTerm f r n) atTop atTop := by
    have hraw :
        Tendsto (fun r : ℝ ↦ ‖wimanTaylorCoefficient f n‖ * r ^ n) atTop atTop :=
      tendsto_const_mul_pow_atTop hn hcoeffnorm
    refine hraw.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp only [wimanTerm, abs_of_nonneg hr]
  refine tendsto_atTop_mono' atTop ?_ hterm
  filter_upwards with r
  exact wimanTerm_le_wimanMaximumTerm f hf r n

/-- **The maximum term eventually exceeds one.** Let $f$ be an entire function that is not a
polynomial function, with Taylor coefficients $a_n$ at the origin and maximum term
$\mu(r) = \sup_n |a_n|\,|r|^n$. Then there is $R$ such that $\mu(r) > 1$ for all real $r \ge R$. -/
theorem eventually_one_lt_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∀ᶠ r : ℝ in atTop, 1 < wimanMaximumTerm f r :=
  (tendsto_wimanMaximumTerm_atTop f hf htrans).eventually (eventually_gt_atTop 1)

/-- **The logarithm of the maximum term is eventually positive.** Let $f$ be an entire function
that is not a polynomial function, with Taylor coefficients $a_n$ at the origin and maximum term
$\mu(r) = \sup_n |a_n|\,|r|^n$. Then there is $R$ such that $\log \mu(r) > 0$ for all real
$r \ge R$. -/
theorem eventually_pos_log_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∀ᶠ r : ℝ in atTop, 0 < Real.log (wimanMaximumTerm f r) := by
  filter_upwards [eventually_one_lt_wimanMaximumTerm f hf htrans] with r hr
  exact Real.log_pos hr

end Complex
